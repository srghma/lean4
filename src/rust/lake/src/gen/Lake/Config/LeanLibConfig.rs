// Lean compiler output
// Module: Lake.Config.LeanLibConfig
// Imports: Lean.Compiler.NameMangling Lake.Util.Casing Lake.Build.Facets Lake.Config.LeanConfig Lake.Config.Glob Lake.Config.Meta Lake.Config.Meta
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_append___redArg,
};
use crate::r#gen::Lake::Build::Facets::{
    initialize_Lake_Build_Facets, l_Lake_LeanLib_leanArtsFacet, l_Lake_Module_oExportFacet,
    l_Lake_Module_oFacet, runtime_initialize_Lake_Build_Facets,
};
use crate::r#gen::Lake::Config::Glob::{
    initialize_Lake_Config_Glob, l_Lake_Glob_matches, runtime_initialize_Lake_Config_Glob,
};
use crate::r#gen::Lake::Config::LeanConfig::{
    initialize_Lake_Config_LeanConfig, l_Lake_LeanConfig___fields,
    l_Lake_instInhabitedLeanConfig_default, runtime_initialize_Lake_Config_LeanConfig,
};
use crate::r#gen::Lake::Config::Meta::{
    initialize_Lake_Config_Meta, runtime_initialize_Lake_Config_Meta,
};
use crate::r#gen::Lake::Util::Casing::{
    initialize_Lake_Util_Casing, runtime_initialize_Lake_Util_Casing,
};
use crate::r#gen::Lean::Compiler::NameMangling::{
    initialize_Lean_Compiler_NameMangling, runtime_initialize_Lean_Compiler_NameMangling,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isPrefixOf;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg;
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
    lean_nat_dec_lt, lean_usize_dec_eq,
};
pub static l_Lake_instInhabitedLeanLibConfig_default___closed__0_value:
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
    m_fun: l_Lake_instInhabitedLeanLibConfig_default___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instInhabitedLeanLibConfig_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanLibConfig_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedLeanLibConfig_default___closed__1_value:
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
    m_data: [46, 0],
};
static mut l_Lake_instInhabitedLeanLibConfig_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanLibConfig_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedLeanLibConfig_default___closed__2_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
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
static mut l_Lake_instInhabitedLeanLibConfig_default___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanLibConfig_default___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedLeanLibConfig_default___closed__3_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lake_instInhabitedLeanLibConfig_default___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanLibConfig_default___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instInhabitedLeanLibConfig_default___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLeanLibConfig_default___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanLibConfig_srcDir___proj___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanLibConfig_srcDir___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_srcDir___proj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_srcDir___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_srcDir___proj___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanLibConfig_srcDir___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_srcDir___proj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_srcDir___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_srcDir___proj___closed__2_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanLibConfig_srcDir___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_srcDir___proj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_srcDir___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_srcDir___proj___closed__3_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanLibConfig_srcDir___proj___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_srcDir___proj___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_srcDir___proj___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_srcDir___proj___closed__4_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanLibConfig_srcDir___proj___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig_srcDir___proj___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig_srcDir___proj___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig_srcDir___proj___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig_srcDir___proj___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_srcDir___proj___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_roots___proj___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanLibConfig_roots___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanLibConfig_roots___proj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_roots___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_roots___proj___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanLibConfig_roots___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanLibConfig_roots___proj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_roots___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_roots___proj___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanLibConfig_roots___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanLibConfig_roots___proj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_roots___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_globs___proj___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanLibConfig_globs___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanLibConfig_globs___proj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_globs___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_globs___proj___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanLibConfig_globs___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanLibConfig_globs___proj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_globs___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_globs___proj___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanLibConfig_globs___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanLibConfig_globs___proj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_globs___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_globs___proj___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanLibConfig_globs___proj___lam__3 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanLibConfig_globs___proj___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_globs___proj___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_globs___proj___closed__4_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanLibConfig_globs___proj___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig_globs___proj___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig_globs___proj___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig_globs___proj___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig_globs___proj___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_globs___proj___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_libName___proj___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanLibConfig_libName___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_libName___proj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_libName___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_libName___proj___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanLibConfig_libName___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_libName___proj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_libName___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_libName___proj___closed__2_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanLibConfig_libName___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_libName___proj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_libName___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_libName___proj___closed__3_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanLibConfig_libName___proj___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_libName___proj___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_libName___proj___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_libName___proj___closed__4_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanLibConfig_libName___proj___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig_libName___proj___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig_libName___proj___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig_libName___proj___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig_libName___proj___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_libName___proj___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0_value:
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
    m_fun: l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__1_value:
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
    m_fun: l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__2_value:
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
    m_fun: l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__3_value:
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
    m_fun: l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__3___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__4_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_needs___proj___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanLibConfig_needs___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanLibConfig_needs___proj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_needs___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_needs___proj___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanLibConfig_needs___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanLibConfig_needs___proj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_needs___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_needs___proj___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanLibConfig_needs___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanLibConfig_needs___proj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_needs___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_needs___proj___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanLibConfig_needs___proj___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanLibConfig_needs___proj___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_needs___proj___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_needs___proj___closed__4_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanLibConfig_needs___proj___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig_needs___proj___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig_needs___proj___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig_needs___proj___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig_needs___proj___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_needs___proj___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0_value:
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
    m_fun: l_Lake_LeanLibConfig_extraDepTargets___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_extraDepTargets___proj___closed__1_value:
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
    m_fun: l_Lake_LeanLibConfig_extraDepTargets___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_extraDepTargets___proj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_extraDepTargets___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_extraDepTargets___proj___closed__2_value:
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
    m_fun: l_Lake_LeanLibConfig_extraDepTargets___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_extraDepTargets___proj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_extraDepTargets___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_extraDepTargets___proj___closed__3_value:
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
    m_fun: l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_extraDepTargets___proj___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_extraDepTargets___proj___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_extraDepTargets___proj___closed__4_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanLibConfig_extraDepTargets___proj___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_extraDepTargets___proj___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_extraDepTargets___proj___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_extraDepTargets___proj___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_LeanLibConfig_extraDepTargets___proj___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_extraDepTargets___proj___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_precompileModules___proj___closed__0_value:
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
    m_fun: l_Lake_LeanLibConfig_precompileModules___proj___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_precompileModules___proj___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_precompileModules___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_precompileModules___proj___closed__1_value:
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
    m_fun: l_Lake_LeanLibConfig_precompileModules___proj___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_precompileModules___proj___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_precompileModules___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_precompileModules___proj___closed__2_value:
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
    m_fun: l_Lake_LeanLibConfig_precompileModules___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_precompileModules___proj___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_precompileModules___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_precompileModules___proj___closed__3_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanLibConfig_precompileModules___proj___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_precompileModules___proj___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_precompileModules___proj___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_LeanLibConfig_precompileModules___proj___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_precompileModules___proj___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_defaultFacets___proj___closed__0_value:
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
    m_fun: l_Lake_LeanLibConfig_defaultFacets___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_defaultFacets___proj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_defaultFacets___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_defaultFacets___proj___closed__1_value:
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
    m_fun: l_Lake_LeanLibConfig_defaultFacets___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_defaultFacets___proj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_defaultFacets___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_defaultFacets___proj___closed__2_value:
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
    m_fun: l_Lake_LeanLibConfig_defaultFacets___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_defaultFacets___proj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_defaultFacets___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_defaultFacets___proj___closed__3_value:
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
    m_fun: l_Lake_LeanLibConfig_defaultFacets___proj___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_defaultFacets___proj___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_defaultFacets___proj___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_defaultFacets___proj___closed__4_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanLibConfig_defaultFacets___proj___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_defaultFacets___proj___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_defaultFacets___proj___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_defaultFacets___proj___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_LeanLibConfig_defaultFacets___proj___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_defaultFacets___proj___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_nativeFacets___proj___closed__0_value:
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
    m_fun: l_Lake_LeanLibConfig_nativeFacets___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_nativeFacets___proj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_nativeFacets___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_nativeFacets___proj___closed__1_value:
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
    m_fun: l_Lake_LeanLibConfig_nativeFacets___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_nativeFacets___proj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_nativeFacets___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_nativeFacets___proj___closed__2_value:
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
    m_fun: l_Lake_LeanLibConfig_nativeFacets___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_nativeFacets___proj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_nativeFacets___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_nativeFacets___proj___closed__3_value:
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
    m_fun: l_Lake_LeanLibConfig_nativeFacets___proj___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_nativeFacets___proj___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_nativeFacets___proj___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_nativeFacets___proj___closed__4_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanLibConfig_nativeFacets___proj___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_nativeFacets___proj___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_nativeFacets___proj___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_nativeFacets___proj___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_LeanLibConfig_nativeFacets___proj___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_nativeFacets___proj___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_allowImportAll___proj___closed__0_value:
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
    m_fun: l_Lake_LeanLibConfig_allowImportAll___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_allowImportAll___proj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_allowImportAll___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_allowImportAll___proj___closed__1_value:
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
    m_fun: l_Lake_LeanLibConfig_allowImportAll___proj___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_allowImportAll___proj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_allowImportAll___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_allowImportAll___proj___closed__2_value:
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
    m_fun: l_Lake_LeanLibConfig_allowImportAll___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_allowImportAll___proj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_allowImportAll___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_allowImportAll___proj___closed__3_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanLibConfig_allowImportAll___proj___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_allowImportAll___proj___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_allowImportAll___proj___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_LeanLibConfig_allowImportAll___proj___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_allowImportAll___proj___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__1_value:
    crate::leanh::LeanCtorObject<14> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13
            + 8) as u16,
        other: 13,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        515 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0_value:
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
    m_fun: l_Lake_LeanLibConfig_toLeanConfig___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_toLeanConfig___proj___closed__1_value:
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
    m_fun: l_Lake_LeanLibConfig_toLeanConfig___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_toLeanConfig___proj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_toLeanConfig___proj___closed__2_value:
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
    m_fun: l_Lake_LeanLibConfig_toLeanConfig___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_toLeanConfig___proj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_toLeanConfig___proj___closed__3_value:
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
    m_fun: l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_toLeanConfig___proj___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_toLeanConfig___proj___closed__4_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_LeanLibConfig_toLeanConfig___proj___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_toLeanConfig___proj___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lake_LeanLibConfig___fields___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__1_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_LeanLibConfig___fields___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__1_value)
                as *mut crate::leanh::LeanObject,
            10458569134091399506 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__2_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanLibConfig___fields___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanLibConfig___fields___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanLibConfig___fields___closed__5_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [114, 111, 111, 116, 115, 0],
    };
static mut l_Lake_LeanLibConfig___fields___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__5_value)
                as *mut crate::leanh::LeanObject,
            12711189428111529632 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__7_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__6_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanLibConfig___fields___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanLibConfig___fields___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanLibConfig___fields___closed__9_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [103, 108, 111, 98, 115, 0],
    };
static mut l_Lake_LeanLibConfig___fields___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__10_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__9_value)
                as *mut crate::leanh::LeanObject,
            1395762918886096898 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__11_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__10_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanLibConfig___fields___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanLibConfig___fields___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanLibConfig___fields___closed__13_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [108, 105, 98, 78, 97, 109, 101, 0],
    };
static mut l_Lake_LeanLibConfig___fields___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__14_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__13_value)
                as *mut crate::leanh::LeanObject,
            10953762620366826259 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__15_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__14_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__14_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanLibConfig___fields___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanLibConfig___fields___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanLibConfig___fields___closed__17_value: crate::leanh::LeanStringObject<19> =
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
            108, 105, 98, 80, 114, 101, 102, 105, 120, 79, 110, 87, 105, 110, 100, 111, 119, 115, 0,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__18_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__17_value)
                as *mut crate::leanh::LeanObject,
            2499362231896656666 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__19_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__18_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__18_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__19_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanLibConfig___fields___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanLibConfig___fields___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanLibConfig___fields___closed__21_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [110, 101, 101, 100, 115, 0],
    };
static mut l_Lake_LeanLibConfig___fields___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__22_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__21_value)
                as *mut crate::leanh::LeanObject,
            14359248566632897495 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__23_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__22_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__22_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__23_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanLibConfig___fields___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanLibConfig___fields___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanLibConfig___fields___closed__25_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            101, 120, 116, 114, 97, 68, 101, 112, 84, 97, 114, 103, 101, 116, 115, 0,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__26_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__25_value)
                as *mut crate::leanh::LeanObject,
            376106234249747944 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__27_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__26_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__26_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__27_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanLibConfig___fields___closed__28_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanLibConfig___fields___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanLibConfig___fields___closed__29_value: crate::leanh::LeanStringObject<18> =
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
            112, 114, 101, 99, 111, 109, 112, 105, 108, 101, 77, 111, 100, 117, 108, 101, 115, 0,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__30_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__29_value)
                as *mut crate::leanh::LeanObject,
            3312148904105101522 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__31_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__30_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__30_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__31_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanLibConfig___fields___closed__32_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanLibConfig___fields___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanLibConfig___fields___closed__33_value: crate::leanh::LeanStringObject<14> =
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
            100, 101, 102, 97, 117, 108, 116, 70, 97, 99, 101, 116, 115, 0,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__34_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__33_value)
                as *mut crate::leanh::LeanObject,
            9682760818844387658 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__34_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__35_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__34_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__34_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__35_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanLibConfig___fields___closed__36_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanLibConfig___fields___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanLibConfig___fields___closed__37_value: crate::leanh::LeanStringObject<13> =
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
        m_data: [110, 97, 116, 105, 118, 101, 70, 97, 99, 101, 116, 115, 0],
    };
static mut l_Lake_LeanLibConfig___fields___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__37_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__38_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__37_value)
                as *mut crate::leanh::LeanObject,
            2134236907718250370 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__38_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__39_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__38_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__38_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__39_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanLibConfig___fields___closed__40_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanLibConfig___fields___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanLibConfig___fields___closed__41_value: crate::leanh::LeanStringObject<15> =
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
        m_data: [
            97, 108, 108, 111, 119, 73, 109, 112, 111, 114, 116, 65, 108, 108, 0,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__41_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__42_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__41_value)
                as *mut crate::leanh::LeanObject,
            15135520235023222771 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__42_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__43_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__42_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__42_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__43_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanLibConfig___fields___closed__44_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanLibConfig___fields___closed__44: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_LeanLibConfig___fields___closed__45_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanLibConfig___fields___closed__45: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanLibConfig___fields___closed__46_value: crate::leanh::LeanStringObject<13> =
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
        m_data: [116, 111, 76, 101, 97, 110, 67, 111, 110, 102, 105, 103, 0],
    };
static mut l_Lake_LeanLibConfig___fields___closed__46: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__46_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__47_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__46_value)
                as *mut crate::leanh::LeanObject,
            782171420137495241 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__47: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__47_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig___fields___closed__48_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__47_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__47_value)
                as *mut crate::leanh::LeanObject,
            256 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig___fields___closed__48: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig___fields___closed__48_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanLibConfig___fields___closed__49_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanLibConfig___fields___closed__49: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_LeanLibConfig___fields: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_LeanLibConfig_instConfigInfo___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanLibConfig_instConfigInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanLibConfig_instConfigInfo___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_instConfigInfo___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_instConfigInfo___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_instConfigInfo___closed__2_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_instConfigInfo___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_instConfigInfo___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_instConfigInfo___closed__3_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_instConfigInfo___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_instConfigInfo___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_instConfigInfo___closed__4_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_instConfigInfo___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_instConfigInfo___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_instConfigInfo___closed__5_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_instConfigInfo___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_instConfigInfo___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_instConfigInfo___closed__6_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_instConfigInfo___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_instConfigInfo___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_instConfigInfo___closed__7_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_instConfigInfo___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_instConfigInfo___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_instConfigInfo___closed__8_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_LeanLibConfig_instConfigInfo___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig_instConfigInfo___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig_instConfigInfo___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_instConfigInfo___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_instConfigInfo___closed__9_value: crate::leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Lake_LeanLibConfig_instConfigInfo___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig_instConfigInfo___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig_instConfigInfo___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig_instConfigInfo___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig_instConfigInfo___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig_instConfigInfo___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_instConfigInfo___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLibConfig_instConfigInfo___closed__10_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_LeanLibConfig_instConfigInfo___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanLibConfig_instConfigInfo___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanLibConfig_instConfigInfo___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_instConfigInfo___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanLibConfig_instConfigInfo___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanLibConfig_instConfigInfo___closed__11: u8 = 0;
pub static l_Lake_LeanLibConfig_instConfigInfo___closed__12_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanLibConfig_instConfigInfo___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_instConfigInfo___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_instConfigInfo___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanLibConfig_instConfigInfo___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanLibConfig_instConfigInfo___closed__13: u8 = 0;
static mut l_Lake_LeanLibConfig_instConfigInfo___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanLibConfig_instConfigInfo___closed__14: usize = 0;
static mut l_Lake_LeanLibConfig_instConfigInfo___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanLibConfig_instConfigInfo___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_LeanLibConfig_instConfigInfo: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanLibConfig_instEmptyCollection___closed__0_value:
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
    m_fun: l_Lake_LeanLibConfig_instEmptyCollection___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanLibConfig_instEmptyCollection___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLibConfig_instEmptyCollection___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_instInhabitedLeanLibConfig_default___lam__0(
    mut v_shouldExport_1242_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_shouldExport_1242_ == 0 {
                    v___x_1248_ = l_Lake_Module_oFacet;
                    v___y_1244_ = v___x_1248_;
                    state = 1;
                    continue;
                } else {
                    v___x_1249_ = l_Lake_Module_oExportFacet;
                    v___y_1244_ = v___x_1249_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1245_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1246_ = lean_mk_empty_array_with_capacity(v___x_1245_);
                crate::leanh::lean_inc(v___y_1244_);
                v___x_1247_ = lean_array_push(v___x_1246_, v___y_1244_);
                return v___x_1247_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instInhabitedLeanLibConfig_default___lam__0___boxed(
    mut v_shouldExport_1250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_shouldExport_boxed_1251_: u8 = 0;
    let mut v_res_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_shouldExport_boxed_1251_ = (crate::leanh::lean_unbox(v_shouldExport_1250_) as u8);
    v_res_1252_ = l_Lake_instInhabitedLeanLibConfig_default___lam__0(v_shouldExport_boxed_1251_);
    return v_res_1252_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0(
    mut v_sz_1253_: usize,
    mut v_i_1254_: usize,
    mut v_bs_1255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1256_: u8 = 0;
    let mut v_v_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: usize = 0;
    let mut v___x_1262_: usize = 0;
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1256_ = lean_usize_dec_lt(v_i_1254_, v_sz_1253_);
                if v___x_1256_ == 0 {
                    return v_bs_1255_;
                } else {
                    v_v_1257_ = lean_array_uget(v_bs_1255_, v_i_1254_);
                    v___x_1258_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1259_ = lean_array_uset(v_bs_1255_, v_i_1254_, v___x_1258_);
                    v___x_1260_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1260_, 0, v_v_1257_);
                    v___x_1261_ = 1usize;
                    v___x_1262_ = lean_usize_add(v_i_1254_, v___x_1261_);
                    v___x_1263_ = lean_array_uset(v_bs_x27_1259_, v_i_1254_, v___x_1260_);
                    v_i_1254_ = v___x_1262_;
                    v_bs_1255_ = v___x_1263_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0___boxed(
    mut v_sz_1265_: *mut crate::leanh::LeanObject,
    mut v_i_1266_: *mut crate::leanh::LeanObject,
    mut v_bs_1267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1268_: usize = 0;
    let mut v_i_boxed_1269_: usize = 0;
    let mut v_res_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1268_ = crate::leanh::lean_unbox_usize(v_sz_1265_);
    crate::leanh::lean_dec(v_sz_1265_);
    v_i_boxed_1269_ = crate::leanh::lean_unbox_usize(v_i_1266_);
    crate::leanh::lean_dec(v_i_1266_);
    v_res_1270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0(v_sz_boxed_1268_, v_i_boxed_1269_, v_bs_1267_);
    return v_res_1270_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanLibConfig_default___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1276_ = l_Lake_LeanLib_leanArtsFacet;
    v___x_1277_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1278_ = lean_mk_empty_array_with_capacity(v___x_1277_);
    v___x_1279_ = lean_array_push(v___x_1278_, v___x_1276_);
    return v___x_1279_;
}
pub unsafe fn l_Lake_instInhabitedLeanLibConfig_default(
    mut v_name_1280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1287_: usize = 0;
    let mut v___x_1288_: usize = 0;
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: u8 = 0;
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1281_ = l_Lake_instInhabitedLeanLibConfig_default___closed__0;
    v___x_1282_ = l_Lake_instInhabitedLeanConfig_default;
    v___x_1283_ = l_Lake_instInhabitedLeanLibConfig_default___closed__1;
    v___x_1284_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1285_ = lean_mk_empty_array_with_capacity(v___x_1284_);
    v___x_1286_ = lean_array_push(v___x_1285_, v_name_1280_);
    v_sz_1287_ = lean_array_size(v___x_1286_);
    v___x_1288_ = 0usize;
    crate::leanh::lean_inc_ref(v___x_1286_);
    v___x_1289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0(v_sz_1287_, v___x_1288_, v___x_1286_);
    v___x_1290_ = l_Lake_instInhabitedLeanLibConfig_default___closed__2;
    v___x_1291_ = 0;
    v___x_1292_ = l_Lake_instInhabitedLeanLibConfig_default___closed__3;
    v___x_1293_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanLibConfig_default___closed__4),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanLibConfig_default___closed__4_once),
        _init_l_Lake_instInhabitedLeanLibConfig_default___closed__4,
    );
    v___x_1294_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
    crate::leanh::lean_ctor_set(v___x_1294_, 0, v___x_1282_);
    crate::leanh::lean_ctor_set(v___x_1294_, 1, v___x_1283_);
    crate::leanh::lean_ctor_set(v___x_1294_, 2, v___x_1286_);
    crate::leanh::lean_ctor_set(v___x_1294_, 3, v___x_1289_);
    crate::leanh::lean_ctor_set(v___x_1294_, 4, v___x_1290_);
    crate::leanh::lean_ctor_set(v___x_1294_, 5, v___x_1292_);
    crate::leanh::lean_ctor_set(v___x_1294_, 6, v___x_1292_);
    crate::leanh::lean_ctor_set(v___x_1294_, 7, v___x_1293_);
    crate::leanh::lean_ctor_set(v___x_1294_, 8, v___f_1281_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1294_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
        v___x_1291_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1294_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
        v___x_1291_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1294_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
        v___x_1291_,
    );
    return v___x_1294_;
}
pub unsafe fn l_Lake_instInhabitedLeanLibConfig(
    mut v_a_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1296_ = l_Lake_instInhabitedLeanLibConfig_default(v_a_1295_);
    return v___x_1296_;
}
pub unsafe fn l_Lake_LeanLibConfig_srcDir___proj___lam__0(
    mut v_cfg_1297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_srcDir_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_srcDir_1298_ = crate::leanh::lean_ctor_get(v_cfg_1297_, 1);
    crate::leanh::lean_inc_ref(v_srcDir_1298_);
    return v_srcDir_1298_;
}
pub unsafe fn l_Lake_LeanLibConfig_srcDir___proj___lam__0___boxed(
    mut v_cfg_1299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1300_ = l_Lake_LeanLibConfig_srcDir___proj___lam__0(v_cfg_1299_);
    crate::leanh::lean_dec_ref(v_cfg_1299_);
    return v_res_1300_;
}
pub unsafe fn l_Lake_LeanLibConfig_srcDir___proj___lam__1(
    mut v_val_1301_: *mut crate::leanh::LeanObject,
    mut v_cfg_1302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_1307_: u8 = 0;
    let mut v_needs_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_1310_: u8 = 0;
    let mut v_defaultFacets_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_1313_: u8 = 0;
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1316_: u8 = 0;
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1320_: u8 = 0;
    let mut v_unused_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1303_ = crate::leanh::lean_ctor_get(v_cfg_1302_, 0);
                v_roots_1304_ = crate::leanh::lean_ctor_get(v_cfg_1302_, 2);
                v_globs_1305_ = crate::leanh::lean_ctor_get(v_cfg_1302_, 3);
                v_libName_1306_ = crate::leanh::lean_ctor_get(v_cfg_1302_, 4);
                v_libPrefixOnWindows_1307_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1302_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_needs_1308_ = crate::leanh::lean_ctor_get(v_cfg_1302_, 5);
                v_extraDepTargets_1309_ = crate::leanh::lean_ctor_get(v_cfg_1302_, 6);
                v_precompileModules_1310_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1302_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_defaultFacets_1311_ = crate::leanh::lean_ctor_get(v_cfg_1302_, 7);
                v_nativeFacets_1312_ = crate::leanh::lean_ctor_get(v_cfg_1302_, 8);
                v_allowImportAll_1313_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1302_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_1320_ = (!crate::leanh::lean_is_exclusive(v_cfg_1302_)) as u8;
                if v_isSharedCheck_1320_ == 0 {
                    v_unused_1321_ = crate::leanh::lean_ctor_get(v_cfg_1302_, 1);
                    crate::leanh::lean_dec(v_unused_1321_);
                    v___x_1315_ = v_cfg_1302_;
                    v_isShared_1316_ = v_isSharedCheck_1320_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1312_);
                    crate::leanh::lean_inc(v_defaultFacets_1311_);
                    crate::leanh::lean_inc(v_extraDepTargets_1309_);
                    crate::leanh::lean_inc(v_needs_1308_);
                    crate::leanh::lean_inc(v_libName_1306_);
                    crate::leanh::lean_inc(v_globs_1305_);
                    crate::leanh::lean_inc(v_roots_1304_);
                    crate::leanh::lean_inc(v_toLeanConfig_1303_);
                    crate::leanh::lean_dec(v_cfg_1302_);
                    v___x_1315_ = crate::leanh::lean_box(0);
                    v_isShared_1316_ = v_isSharedCheck_1320_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1316_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1315_, 1, v_val_1301_);
                    v___x_1318_ = v___x_1315_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1319_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_toLeanConfig_1303_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_val_1301_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1319_, 2, v_roots_1304_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1319_, 3, v_globs_1305_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1319_, 4, v_libName_1306_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1319_, 5, v_needs_1308_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1319_, 6, v_extraDepTargets_1309_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1319_, 7, v_defaultFacets_1311_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1319_, 8, v_nativeFacets_1312_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1319_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_libPrefixOnWindows_1307_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1319_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                        v_precompileModules_1310_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1319_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                        v_allowImportAll_1313_,
                    );
                    v___x_1318_ = v_reuseFailAlloc_1319_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1318_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_srcDir___proj___lam__2(
    mut v_f_1322_: *mut crate::leanh::LeanObject,
    mut v_cfg_1323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_1329_: u8 = 0;
    let mut v_needs_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_1332_: u8 = 0;
    let mut v_defaultFacets_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_1335_: u8 = 0;
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1338_: u8 = 0;
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1343_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1324_ = crate::leanh::lean_ctor_get(v_cfg_1323_, 0);
                v_srcDir_1325_ = crate::leanh::lean_ctor_get(v_cfg_1323_, 1);
                v_roots_1326_ = crate::leanh::lean_ctor_get(v_cfg_1323_, 2);
                v_globs_1327_ = crate::leanh::lean_ctor_get(v_cfg_1323_, 3);
                v_libName_1328_ = crate::leanh::lean_ctor_get(v_cfg_1323_, 4);
                v_libPrefixOnWindows_1329_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1323_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_needs_1330_ = crate::leanh::lean_ctor_get(v_cfg_1323_, 5);
                v_extraDepTargets_1331_ = crate::leanh::lean_ctor_get(v_cfg_1323_, 6);
                v_precompileModules_1332_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1323_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_defaultFacets_1333_ = crate::leanh::lean_ctor_get(v_cfg_1323_, 7);
                v_nativeFacets_1334_ = crate::leanh::lean_ctor_get(v_cfg_1323_, 8);
                v_allowImportAll_1335_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1323_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_1343_ = (!crate::leanh::lean_is_exclusive(v_cfg_1323_)) as u8;
                if v_isSharedCheck_1343_ == 0 {
                    v___x_1337_ = v_cfg_1323_;
                    v_isShared_1338_ = v_isSharedCheck_1343_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1334_);
                    crate::leanh::lean_inc(v_defaultFacets_1333_);
                    crate::leanh::lean_inc(v_extraDepTargets_1331_);
                    crate::leanh::lean_inc(v_needs_1330_);
                    crate::leanh::lean_inc(v_libName_1328_);
                    crate::leanh::lean_inc(v_globs_1327_);
                    crate::leanh::lean_inc(v_roots_1326_);
                    crate::leanh::lean_inc(v_srcDir_1325_);
                    crate::leanh::lean_inc(v_toLeanConfig_1324_);
                    crate::leanh::lean_dec(v_cfg_1323_);
                    v___x_1337_ = crate::leanh::lean_box(0);
                    v_isShared_1338_ = v_isSharedCheck_1343_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1339_ = crate::leanh::lean_apply_1(v_f_1322_, v_srcDir_1325_);
                if v_isShared_1338_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1337_, 1, v___x_1339_);
                    v___x_1341_ = v___x_1337_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1342_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_toLeanConfig_1324_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 1, v___x_1339_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 2, v_roots_1326_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 3, v_globs_1327_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 4, v_libName_1328_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 5, v_needs_1330_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 6, v_extraDepTargets_1331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 7, v_defaultFacets_1333_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 8, v_nativeFacets_1334_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1342_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_libPrefixOnWindows_1329_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1342_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                        v_precompileModules_1332_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1342_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                        v_allowImportAll_1335_,
                    );
                    v___x_1341_ = v_reuseFailAlloc_1342_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1341_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_srcDir___proj___lam__3(
    mut v_x_1344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1345_ = l_Lake_instInhabitedLeanLibConfig_default___closed__1;
    return v___x_1345_;
}
pub unsafe fn l_Lake_LeanLibConfig_srcDir___proj___lam__3___boxed(
    mut v_x_1346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1347_ = l_Lake_LeanLibConfig_srcDir___proj___lam__3(v_x_1346_);
    crate::leanh::lean_dec_ref(v_x_1346_);
    return v_res_1347_;
}
pub unsafe fn l_Lake_LeanLibConfig_srcDir___proj(
    mut v_name_1357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1358_ = l_Lake_LeanLibConfig_srcDir___proj___closed__4;
    return v___x_1358_;
}
pub unsafe fn l_Lake_LeanLibConfig_srcDir___proj___boxed(
    mut v_name_1359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1360_ = l_Lake_LeanLibConfig_srcDir___proj(v_name_1359_);
    crate::leanh::lean_dec(v_name_1359_);
    return v_res_1360_;
}
pub unsafe fn l_Lake_LeanLibConfig_srcDir_instConfigField(
    mut v_name_1361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1362_ = l_Lake_LeanLibConfig_srcDir___proj(v_name_1361_);
    return v___x_1362_;
}
pub unsafe fn l_Lake_LeanLibConfig_srcDir_instConfigField___boxed(
    mut v_name_1363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1364_ = l_Lake_LeanLibConfig_srcDir_instConfigField(v_name_1363_);
    crate::leanh::lean_dec(v_name_1363_);
    return v_res_1364_;
}
pub unsafe fn l_Lake_LeanLibConfig_roots___proj___lam__0(
    mut v_cfg_1365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_roots_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_roots_1366_ = crate::leanh::lean_ctor_get(v_cfg_1365_, 2);
    crate::leanh::lean_inc_ref(v_roots_1366_);
    return v_roots_1366_;
}
pub unsafe fn l_Lake_LeanLibConfig_roots___proj___lam__0___boxed(
    mut v_cfg_1367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1368_ = l_Lake_LeanLibConfig_roots___proj___lam__0(v_cfg_1367_);
    crate::leanh::lean_dec_ref(v_cfg_1367_);
    return v_res_1368_;
}
pub unsafe fn l_Lake_LeanLibConfig_roots___proj___lam__1(
    mut v_val_1369_: *mut crate::leanh::LeanObject,
    mut v_cfg_1370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_1375_: u8 = 0;
    let mut v_needs_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_1378_: u8 = 0;
    let mut v_defaultFacets_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_1381_: u8 = 0;
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1384_: u8 = 0;
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1388_: u8 = 0;
    let mut v_unused_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1371_ = crate::leanh::lean_ctor_get(v_cfg_1370_, 0);
                v_srcDir_1372_ = crate::leanh::lean_ctor_get(v_cfg_1370_, 1);
                v_globs_1373_ = crate::leanh::lean_ctor_get(v_cfg_1370_, 3);
                v_libName_1374_ = crate::leanh::lean_ctor_get(v_cfg_1370_, 4);
                v_libPrefixOnWindows_1375_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1370_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_needs_1376_ = crate::leanh::lean_ctor_get(v_cfg_1370_, 5);
                v_extraDepTargets_1377_ = crate::leanh::lean_ctor_get(v_cfg_1370_, 6);
                v_precompileModules_1378_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1370_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_defaultFacets_1379_ = crate::leanh::lean_ctor_get(v_cfg_1370_, 7);
                v_nativeFacets_1380_ = crate::leanh::lean_ctor_get(v_cfg_1370_, 8);
                v_allowImportAll_1381_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1370_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_1388_ = (!crate::leanh::lean_is_exclusive(v_cfg_1370_)) as u8;
                if v_isSharedCheck_1388_ == 0 {
                    v_unused_1389_ = crate::leanh::lean_ctor_get(v_cfg_1370_, 2);
                    crate::leanh::lean_dec(v_unused_1389_);
                    v___x_1383_ = v_cfg_1370_;
                    v_isShared_1384_ = v_isSharedCheck_1388_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1380_);
                    crate::leanh::lean_inc(v_defaultFacets_1379_);
                    crate::leanh::lean_inc(v_extraDepTargets_1377_);
                    crate::leanh::lean_inc(v_needs_1376_);
                    crate::leanh::lean_inc(v_libName_1374_);
                    crate::leanh::lean_inc(v_globs_1373_);
                    crate::leanh::lean_inc(v_srcDir_1372_);
                    crate::leanh::lean_inc(v_toLeanConfig_1371_);
                    crate::leanh::lean_dec(v_cfg_1370_);
                    v___x_1383_ = crate::leanh::lean_box(0);
                    v_isShared_1384_ = v_isSharedCheck_1388_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1384_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1383_, 2, v_val_1369_);
                    v___x_1386_ = v___x_1383_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1387_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_toLeanConfig_1371_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1387_, 1, v_srcDir_1372_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1387_, 2, v_val_1369_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1387_, 3, v_globs_1373_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1387_, 4, v_libName_1374_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1387_, 5, v_needs_1376_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1387_, 6, v_extraDepTargets_1377_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1387_, 7, v_defaultFacets_1379_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1387_, 8, v_nativeFacets_1380_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1387_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_libPrefixOnWindows_1375_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1387_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                        v_precompileModules_1378_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1387_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                        v_allowImportAll_1381_,
                    );
                    v___x_1386_ = v_reuseFailAlloc_1387_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1386_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_roots___proj___lam__2(
    mut v_f_1390_: *mut crate::leanh::LeanObject,
    mut v_cfg_1391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_1397_: u8 = 0;
    let mut v_needs_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_1400_: u8 = 0;
    let mut v_defaultFacets_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_1403_: u8 = 0;
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1406_: u8 = 0;
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1411_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1392_ = crate::leanh::lean_ctor_get(v_cfg_1391_, 0);
                v_srcDir_1393_ = crate::leanh::lean_ctor_get(v_cfg_1391_, 1);
                v_roots_1394_ = crate::leanh::lean_ctor_get(v_cfg_1391_, 2);
                v_globs_1395_ = crate::leanh::lean_ctor_get(v_cfg_1391_, 3);
                v_libName_1396_ = crate::leanh::lean_ctor_get(v_cfg_1391_, 4);
                v_libPrefixOnWindows_1397_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1391_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_needs_1398_ = crate::leanh::lean_ctor_get(v_cfg_1391_, 5);
                v_extraDepTargets_1399_ = crate::leanh::lean_ctor_get(v_cfg_1391_, 6);
                v_precompileModules_1400_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1391_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_defaultFacets_1401_ = crate::leanh::lean_ctor_get(v_cfg_1391_, 7);
                v_nativeFacets_1402_ = crate::leanh::lean_ctor_get(v_cfg_1391_, 8);
                v_allowImportAll_1403_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1391_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_1411_ = (!crate::leanh::lean_is_exclusive(v_cfg_1391_)) as u8;
                if v_isSharedCheck_1411_ == 0 {
                    v___x_1405_ = v_cfg_1391_;
                    v_isShared_1406_ = v_isSharedCheck_1411_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1402_);
                    crate::leanh::lean_inc(v_defaultFacets_1401_);
                    crate::leanh::lean_inc(v_extraDepTargets_1399_);
                    crate::leanh::lean_inc(v_needs_1398_);
                    crate::leanh::lean_inc(v_libName_1396_);
                    crate::leanh::lean_inc(v_globs_1395_);
                    crate::leanh::lean_inc(v_roots_1394_);
                    crate::leanh::lean_inc(v_srcDir_1393_);
                    crate::leanh::lean_inc(v_toLeanConfig_1392_);
                    crate::leanh::lean_dec(v_cfg_1391_);
                    v___x_1405_ = crate::leanh::lean_box(0);
                    v_isShared_1406_ = v_isSharedCheck_1411_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1407_ = crate::leanh::lean_apply_1(v_f_1390_, v_roots_1394_);
                if v_isShared_1406_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1405_, 2, v___x_1407_);
                    v___x_1409_ = v___x_1405_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1410_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_toLeanConfig_1392_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_srcDir_1393_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 2, v___x_1407_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 3, v_globs_1395_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 4, v_libName_1396_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 5, v_needs_1398_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 6, v_extraDepTargets_1399_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 7, v_defaultFacets_1401_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 8, v_nativeFacets_1402_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1410_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_libPrefixOnWindows_1397_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1410_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                        v_precompileModules_1400_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1410_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                        v_allowImportAll_1403_,
                    );
                    v___x_1409_ = v_reuseFailAlloc_1410_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1409_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_roots___proj___lam__3(
    mut v_name_1412_: *mut crate::leanh::LeanObject,
    mut v_x_1413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1414_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1415_ = lean_mk_empty_array_with_capacity(v___x_1414_);
    v___x_1416_ = lean_array_push(v___x_1415_, v_name_1412_);
    return v___x_1416_;
}
pub unsafe fn l_Lake_LeanLibConfig_roots___proj___lam__3___boxed(
    mut v_name_1417_: *mut crate::leanh::LeanObject,
    mut v_x_1418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1419_ = l_Lake_LeanLibConfig_roots___proj___lam__3(v_name_1417_, v_x_1418_);
    crate::leanh::lean_dec_ref(v_x_1418_);
    return v_res_1419_;
}
pub unsafe fn l_Lake_LeanLibConfig_roots___proj(
    mut v_name_1423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1424_ = l_Lake_LeanLibConfig_roots___proj___closed__0;
    v___f_1425_ = l_Lake_LeanLibConfig_roots___proj___closed__1;
    v___f_1426_ = l_Lake_LeanLibConfig_roots___proj___closed__2;
    v___f_1427_ = crate::leanh::lean_alloc_closure(
        l_Lake_LeanLibConfig_roots___proj___lam__3___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1427_, 0, v_name_1423_);
    v___x_1428_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1428_, 0, v___f_1424_);
    crate::leanh::lean_ctor_set(v___x_1428_, 1, v___f_1425_);
    crate::leanh::lean_ctor_set(v___x_1428_, 2, v___f_1426_);
    crate::leanh::lean_ctor_set(v___x_1428_, 3, v___f_1427_);
    return v___x_1428_;
}
pub unsafe fn l_Lake_LeanLibConfig_roots_instConfigField(
    mut v_name_1429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1430_ = l_Lake_LeanLibConfig_roots___proj(v_name_1429_);
    return v___x_1430_;
}
pub unsafe fn l_Lake_LeanLibConfig_globs___proj___lam__0(
    mut v_cfg_1431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_globs_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_globs_1432_ = crate::leanh::lean_ctor_get(v_cfg_1431_, 3);
    crate::leanh::lean_inc_ref(v_globs_1432_);
    return v_globs_1432_;
}
pub unsafe fn l_Lake_LeanLibConfig_globs___proj___lam__0___boxed(
    mut v_cfg_1433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1434_ = l_Lake_LeanLibConfig_globs___proj___lam__0(v_cfg_1433_);
    crate::leanh::lean_dec_ref(v_cfg_1433_);
    return v_res_1434_;
}
pub unsafe fn l_Lake_LeanLibConfig_globs___proj___lam__1(
    mut v_val_1435_: *mut crate::leanh::LeanObject,
    mut v_cfg_1436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_1441_: u8 = 0;
    let mut v_needs_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_1444_: u8 = 0;
    let mut v_defaultFacets_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_1447_: u8 = 0;
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1450_: u8 = 0;
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1454_: u8 = 0;
    let mut v_unused_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1437_ = crate::leanh::lean_ctor_get(v_cfg_1436_, 0);
                v_srcDir_1438_ = crate::leanh::lean_ctor_get(v_cfg_1436_, 1);
                v_roots_1439_ = crate::leanh::lean_ctor_get(v_cfg_1436_, 2);
                v_libName_1440_ = crate::leanh::lean_ctor_get(v_cfg_1436_, 4);
                v_libPrefixOnWindows_1441_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1436_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_needs_1442_ = crate::leanh::lean_ctor_get(v_cfg_1436_, 5);
                v_extraDepTargets_1443_ = crate::leanh::lean_ctor_get(v_cfg_1436_, 6);
                v_precompileModules_1444_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1436_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_defaultFacets_1445_ = crate::leanh::lean_ctor_get(v_cfg_1436_, 7);
                v_nativeFacets_1446_ = crate::leanh::lean_ctor_get(v_cfg_1436_, 8);
                v_allowImportAll_1447_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1436_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_1454_ = (!crate::leanh::lean_is_exclusive(v_cfg_1436_)) as u8;
                if v_isSharedCheck_1454_ == 0 {
                    v_unused_1455_ = crate::leanh::lean_ctor_get(v_cfg_1436_, 3);
                    crate::leanh::lean_dec(v_unused_1455_);
                    v___x_1449_ = v_cfg_1436_;
                    v_isShared_1450_ = v_isSharedCheck_1454_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1446_);
                    crate::leanh::lean_inc(v_defaultFacets_1445_);
                    crate::leanh::lean_inc(v_extraDepTargets_1443_);
                    crate::leanh::lean_inc(v_needs_1442_);
                    crate::leanh::lean_inc(v_libName_1440_);
                    crate::leanh::lean_inc(v_roots_1439_);
                    crate::leanh::lean_inc(v_srcDir_1438_);
                    crate::leanh::lean_inc(v_toLeanConfig_1437_);
                    crate::leanh::lean_dec(v_cfg_1436_);
                    v___x_1449_ = crate::leanh::lean_box(0);
                    v_isShared_1450_ = v_isSharedCheck_1454_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1450_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1449_, 3, v_val_1435_);
                    v___x_1452_ = v___x_1449_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1453_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_toLeanConfig_1437_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_srcDir_1438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 2, v_roots_1439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 3, v_val_1435_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 4, v_libName_1440_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 5, v_needs_1442_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 6, v_extraDepTargets_1443_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 7, v_defaultFacets_1445_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 8, v_nativeFacets_1446_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1453_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_libPrefixOnWindows_1441_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1453_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                        v_precompileModules_1444_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1453_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                        v_allowImportAll_1447_,
                    );
                    v___x_1452_ = v_reuseFailAlloc_1453_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1452_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_globs___proj___lam__2(
    mut v_f_1456_: *mut crate::leanh::LeanObject,
    mut v_cfg_1457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_1463_: u8 = 0;
    let mut v_needs_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_1466_: u8 = 0;
    let mut v_defaultFacets_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_1469_: u8 = 0;
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1472_: u8 = 0;
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1477_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1458_ = crate::leanh::lean_ctor_get(v_cfg_1457_, 0);
                v_srcDir_1459_ = crate::leanh::lean_ctor_get(v_cfg_1457_, 1);
                v_roots_1460_ = crate::leanh::lean_ctor_get(v_cfg_1457_, 2);
                v_globs_1461_ = crate::leanh::lean_ctor_get(v_cfg_1457_, 3);
                v_libName_1462_ = crate::leanh::lean_ctor_get(v_cfg_1457_, 4);
                v_libPrefixOnWindows_1463_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1457_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_needs_1464_ = crate::leanh::lean_ctor_get(v_cfg_1457_, 5);
                v_extraDepTargets_1465_ = crate::leanh::lean_ctor_get(v_cfg_1457_, 6);
                v_precompileModules_1466_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1457_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_defaultFacets_1467_ = crate::leanh::lean_ctor_get(v_cfg_1457_, 7);
                v_nativeFacets_1468_ = crate::leanh::lean_ctor_get(v_cfg_1457_, 8);
                v_allowImportAll_1469_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1457_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_1477_ = (!crate::leanh::lean_is_exclusive(v_cfg_1457_)) as u8;
                if v_isSharedCheck_1477_ == 0 {
                    v___x_1471_ = v_cfg_1457_;
                    v_isShared_1472_ = v_isSharedCheck_1477_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1468_);
                    crate::leanh::lean_inc(v_defaultFacets_1467_);
                    crate::leanh::lean_inc(v_extraDepTargets_1465_);
                    crate::leanh::lean_inc(v_needs_1464_);
                    crate::leanh::lean_inc(v_libName_1462_);
                    crate::leanh::lean_inc(v_globs_1461_);
                    crate::leanh::lean_inc(v_roots_1460_);
                    crate::leanh::lean_inc(v_srcDir_1459_);
                    crate::leanh::lean_inc(v_toLeanConfig_1458_);
                    crate::leanh::lean_dec(v_cfg_1457_);
                    v___x_1471_ = crate::leanh::lean_box(0);
                    v_isShared_1472_ = v_isSharedCheck_1477_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1473_ = crate::leanh::lean_apply_1(v_f_1456_, v_globs_1461_);
                if v_isShared_1472_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1471_, 3, v___x_1473_);
                    v___x_1475_ = v___x_1471_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1476_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_toLeanConfig_1458_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_srcDir_1459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 2, v_roots_1460_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 3, v___x_1473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 4, v_libName_1462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 5, v_needs_1464_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 6, v_extraDepTargets_1465_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 7, v_defaultFacets_1467_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 8, v_nativeFacets_1468_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1476_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_libPrefixOnWindows_1463_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1476_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                        v_precompileModules_1466_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1476_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                        v_allowImportAll_1469_,
                    );
                    v___x_1475_ = v_reuseFailAlloc_1476_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1475_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_globs___proj___lam__3(
    mut v_x_1478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_roots_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1480_: usize = 0;
    let mut v___x_1481_: usize = 0;
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_roots_1479_ = crate::leanh::lean_ctor_get(v_x_1478_, 2);
    crate::leanh::lean_inc_ref(v_roots_1479_);
    crate::leanh::lean_dec_ref(v_x_1478_);
    v_sz_1480_ = lean_array_size(v_roots_1479_);
    v___x_1481_ = 0usize;
    v___x_1482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_instInhabitedLeanLibConfig_default_spec__0(v_sz_1480_, v___x_1481_, v_roots_1479_);
    return v___x_1482_;
}
pub unsafe fn l_Lake_LeanLibConfig_globs___proj(
    mut v_name_1492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1493_ = l_Lake_LeanLibConfig_globs___proj___closed__4;
    return v___x_1493_;
}
pub unsafe fn l_Lake_LeanLibConfig_globs___proj___boxed(
    mut v_name_1494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1495_ = l_Lake_LeanLibConfig_globs___proj(v_name_1494_);
    crate::leanh::lean_dec(v_name_1494_);
    return v_res_1495_;
}
pub unsafe fn l_Lake_LeanLibConfig_globs_instConfigField(
    mut v_name_1496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1497_ = l_Lake_LeanLibConfig_globs___proj(v_name_1496_);
    return v___x_1497_;
}
pub unsafe fn l_Lake_LeanLibConfig_globs_instConfigField___boxed(
    mut v_name_1498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1499_ = l_Lake_LeanLibConfig_globs_instConfigField(v_name_1498_);
    crate::leanh::lean_dec(v_name_1498_);
    return v_res_1499_;
}
pub unsafe fn l_Lake_LeanLibConfig_libName___proj___lam__0(
    mut v_cfg_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_libName_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_libName_1501_ = crate::leanh::lean_ctor_get(v_cfg_1500_, 4);
    crate::leanh::lean_inc_ref(v_libName_1501_);
    return v_libName_1501_;
}
pub unsafe fn l_Lake_LeanLibConfig_libName___proj___lam__0___boxed(
    mut v_cfg_1502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1503_ = l_Lake_LeanLibConfig_libName___proj___lam__0(v_cfg_1502_);
    crate::leanh::lean_dec_ref(v_cfg_1502_);
    return v_res_1503_;
}
pub unsafe fn l_Lake_LeanLibConfig_libName___proj___lam__1(
    mut v_val_1504_: *mut crate::leanh::LeanObject,
    mut v_cfg_1505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_1510_: u8 = 0;
    let mut v_needs_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_1513_: u8 = 0;
    let mut v_defaultFacets_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_1516_: u8 = 0;
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1519_: u8 = 0;
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1523_: u8 = 0;
    let mut v_unused_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1506_ = crate::leanh::lean_ctor_get(v_cfg_1505_, 0);
                v_srcDir_1507_ = crate::leanh::lean_ctor_get(v_cfg_1505_, 1);
                v_roots_1508_ = crate::leanh::lean_ctor_get(v_cfg_1505_, 2);
                v_globs_1509_ = crate::leanh::lean_ctor_get(v_cfg_1505_, 3);
                v_libPrefixOnWindows_1510_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1505_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_needs_1511_ = crate::leanh::lean_ctor_get(v_cfg_1505_, 5);
                v_extraDepTargets_1512_ = crate::leanh::lean_ctor_get(v_cfg_1505_, 6);
                v_precompileModules_1513_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1505_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_defaultFacets_1514_ = crate::leanh::lean_ctor_get(v_cfg_1505_, 7);
                v_nativeFacets_1515_ = crate::leanh::lean_ctor_get(v_cfg_1505_, 8);
                v_allowImportAll_1516_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1505_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_1523_ = (!crate::leanh::lean_is_exclusive(v_cfg_1505_)) as u8;
                if v_isSharedCheck_1523_ == 0 {
                    v_unused_1524_ = crate::leanh::lean_ctor_get(v_cfg_1505_, 4);
                    crate::leanh::lean_dec(v_unused_1524_);
                    v___x_1518_ = v_cfg_1505_;
                    v_isShared_1519_ = v_isSharedCheck_1523_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1515_);
                    crate::leanh::lean_inc(v_defaultFacets_1514_);
                    crate::leanh::lean_inc(v_extraDepTargets_1512_);
                    crate::leanh::lean_inc(v_needs_1511_);
                    crate::leanh::lean_inc(v_globs_1509_);
                    crate::leanh::lean_inc(v_roots_1508_);
                    crate::leanh::lean_inc(v_srcDir_1507_);
                    crate::leanh::lean_inc(v_toLeanConfig_1506_);
                    crate::leanh::lean_dec(v_cfg_1505_);
                    v___x_1518_ = crate::leanh::lean_box(0);
                    v_isShared_1519_ = v_isSharedCheck_1523_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1519_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1518_, 4, v_val_1504_);
                    v___x_1521_ = v___x_1518_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1522_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_toLeanConfig_1506_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_srcDir_1507_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1522_, 2, v_roots_1508_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1522_, 3, v_globs_1509_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1522_, 4, v_val_1504_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1522_, 5, v_needs_1511_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1522_, 6, v_extraDepTargets_1512_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1522_, 7, v_defaultFacets_1514_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1522_, 8, v_nativeFacets_1515_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1522_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_libPrefixOnWindows_1510_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1522_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                        v_precompileModules_1513_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1522_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                        v_allowImportAll_1516_,
                    );
                    v___x_1521_ = v_reuseFailAlloc_1522_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1521_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_libName___proj___lam__2(
    mut v_f_1525_: *mut crate::leanh::LeanObject,
    mut v_cfg_1526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_1532_: u8 = 0;
    let mut v_needs_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_1535_: u8 = 0;
    let mut v_defaultFacets_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_1538_: u8 = 0;
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1541_: u8 = 0;
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1546_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1527_ = crate::leanh::lean_ctor_get(v_cfg_1526_, 0);
                v_srcDir_1528_ = crate::leanh::lean_ctor_get(v_cfg_1526_, 1);
                v_roots_1529_ = crate::leanh::lean_ctor_get(v_cfg_1526_, 2);
                v_globs_1530_ = crate::leanh::lean_ctor_get(v_cfg_1526_, 3);
                v_libName_1531_ = crate::leanh::lean_ctor_get(v_cfg_1526_, 4);
                v_libPrefixOnWindows_1532_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1526_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_needs_1533_ = crate::leanh::lean_ctor_get(v_cfg_1526_, 5);
                v_extraDepTargets_1534_ = crate::leanh::lean_ctor_get(v_cfg_1526_, 6);
                v_precompileModules_1535_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1526_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_defaultFacets_1536_ = crate::leanh::lean_ctor_get(v_cfg_1526_, 7);
                v_nativeFacets_1537_ = crate::leanh::lean_ctor_get(v_cfg_1526_, 8);
                v_allowImportAll_1538_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1526_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_1546_ = (!crate::leanh::lean_is_exclusive(v_cfg_1526_)) as u8;
                if v_isSharedCheck_1546_ == 0 {
                    v___x_1540_ = v_cfg_1526_;
                    v_isShared_1541_ = v_isSharedCheck_1546_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1537_);
                    crate::leanh::lean_inc(v_defaultFacets_1536_);
                    crate::leanh::lean_inc(v_extraDepTargets_1534_);
                    crate::leanh::lean_inc(v_needs_1533_);
                    crate::leanh::lean_inc(v_libName_1531_);
                    crate::leanh::lean_inc(v_globs_1530_);
                    crate::leanh::lean_inc(v_roots_1529_);
                    crate::leanh::lean_inc(v_srcDir_1528_);
                    crate::leanh::lean_inc(v_toLeanConfig_1527_);
                    crate::leanh::lean_dec(v_cfg_1526_);
                    v___x_1540_ = crate::leanh::lean_box(0);
                    v_isShared_1541_ = v_isSharedCheck_1546_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1542_ = crate::leanh::lean_apply_1(v_f_1525_, v_libName_1531_);
                if v_isShared_1541_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1540_, 4, v___x_1542_);
                    v___x_1544_ = v___x_1540_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1545_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_toLeanConfig_1527_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_srcDir_1528_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_roots_1529_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 3, v_globs_1530_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 4, v___x_1542_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 5, v_needs_1533_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 6, v_extraDepTargets_1534_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 7, v_defaultFacets_1536_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 8, v_nativeFacets_1537_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1545_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_libPrefixOnWindows_1532_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1545_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                        v_precompileModules_1535_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1545_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                        v_allowImportAll_1538_,
                    );
                    v___x_1544_ = v_reuseFailAlloc_1545_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1544_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_libName___proj___lam__3(
    mut v_x_1547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1548_ = l_Lake_instInhabitedLeanLibConfig_default___closed__2;
    return v___x_1548_;
}
pub unsafe fn l_Lake_LeanLibConfig_libName___proj___lam__3___boxed(
    mut v_x_1549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1550_ = l_Lake_LeanLibConfig_libName___proj___lam__3(v_x_1549_);
    crate::leanh::lean_dec_ref(v_x_1549_);
    return v_res_1550_;
}
pub unsafe fn l_Lake_LeanLibConfig_libName___proj(
    mut v_name_1560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1561_ = l_Lake_LeanLibConfig_libName___proj___closed__4;
    return v___x_1561_;
}
pub unsafe fn l_Lake_LeanLibConfig_libName___proj___boxed(
    mut v_name_1562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1563_ = l_Lake_LeanLibConfig_libName___proj(v_name_1562_);
    crate::leanh::lean_dec(v_name_1562_);
    return v_res_1563_;
}
pub unsafe fn l_Lake_LeanLibConfig_libName_instConfigField(
    mut v_name_1564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1565_ = l_Lake_LeanLibConfig_libName___proj(v_name_1564_);
    return v___x_1565_;
}
pub unsafe fn l_Lake_LeanLibConfig_libName_instConfigField___boxed(
    mut v_name_1566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1567_ = l_Lake_LeanLibConfig_libName_instConfigField(v_name_1566_);
    crate::leanh::lean_dec(v_name_1566_);
    return v_res_1567_;
}
pub unsafe fn l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__0(
    mut v_cfg_1568_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_libPrefixOnWindows_1569_: u8 = 0;
    v_libPrefixOnWindows_1569_ = crate::leanh::lean_ctor_get_uint8(
        v_cfg_1568_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
    );
    return v_libPrefixOnWindows_1569_;
}
pub unsafe fn l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__0___boxed(
    mut v_cfg_1570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1571_: u8 = 0;
    let mut v_r_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1571_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__0(v_cfg_1570_);
    crate::leanh::lean_dec_ref(v_cfg_1570_);
    v_r_1572_ = crate::leanh::lean_box((v_res_1571_) as usize);
    return v_r_1572_;
}
pub unsafe fn l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__1(
    mut v_val_1573_: u8,
    mut v_cfg_1574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_1582_: u8 = 0;
    let mut v_defaultFacets_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_1585_: u8 = 0;
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1588_: u8 = 0;
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1592_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1575_ = crate::leanh::lean_ctor_get(v_cfg_1574_, 0);
                v_srcDir_1576_ = crate::leanh::lean_ctor_get(v_cfg_1574_, 1);
                v_roots_1577_ = crate::leanh::lean_ctor_get(v_cfg_1574_, 2);
                v_globs_1578_ = crate::leanh::lean_ctor_get(v_cfg_1574_, 3);
                v_libName_1579_ = crate::leanh::lean_ctor_get(v_cfg_1574_, 4);
                v_needs_1580_ = crate::leanh::lean_ctor_get(v_cfg_1574_, 5);
                v_extraDepTargets_1581_ = crate::leanh::lean_ctor_get(v_cfg_1574_, 6);
                v_precompileModules_1582_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1574_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_defaultFacets_1583_ = crate::leanh::lean_ctor_get(v_cfg_1574_, 7);
                v_nativeFacets_1584_ = crate::leanh::lean_ctor_get(v_cfg_1574_, 8);
                v_allowImportAll_1585_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1574_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_1592_ = (!crate::leanh::lean_is_exclusive(v_cfg_1574_)) as u8;
                if v_isSharedCheck_1592_ == 0 {
                    v___x_1587_ = v_cfg_1574_;
                    v_isShared_1588_ = v_isSharedCheck_1592_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1584_);
                    crate::leanh::lean_inc(v_defaultFacets_1583_);
                    crate::leanh::lean_inc(v_extraDepTargets_1581_);
                    crate::leanh::lean_inc(v_needs_1580_);
                    crate::leanh::lean_inc(v_libName_1579_);
                    crate::leanh::lean_inc(v_globs_1578_);
                    crate::leanh::lean_inc(v_roots_1577_);
                    crate::leanh::lean_inc(v_srcDir_1576_);
                    crate::leanh::lean_inc(v_toLeanConfig_1575_);
                    crate::leanh::lean_dec(v_cfg_1574_);
                    v___x_1587_ = crate::leanh::lean_box(0);
                    v_isShared_1588_ = v_isSharedCheck_1592_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1588_ == 0 {
                    v___x_1590_ = v___x_1587_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1591_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_toLeanConfig_1575_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_srcDir_1576_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1591_, 2, v_roots_1577_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1591_, 3, v_globs_1578_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1591_, 4, v_libName_1579_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1591_, 5, v_needs_1580_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1591_, 6, v_extraDepTargets_1581_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1591_, 7, v_defaultFacets_1583_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1591_, 8, v_nativeFacets_1584_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1591_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                        v_precompileModules_1582_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1591_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                        v_allowImportAll_1585_,
                    );
                    v___x_1590_ = v_reuseFailAlloc_1591_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1590_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                    v_val_1573_,
                );
                return v___x_1590_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__1___boxed(
    mut v_val_1593_: *mut crate::leanh::LeanObject,
    mut v_cfg_1594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_71__boxed_1595_: u8 = 0;
    let mut v_res_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_71__boxed_1595_ = (crate::leanh::lean_unbox(v_val_1593_) as u8);
    v_res_1596_ =
        l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__1(v_val_71__boxed_1595_, v_cfg_1594_);
    return v_res_1596_;
}
pub unsafe fn l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__2(
    mut v_f_1597_: *mut crate::leanh::LeanObject,
    mut v_cfg_1598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_1604_: u8 = 0;
    let mut v_needs_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_1607_: u8 = 0;
    let mut v_defaultFacets_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_1610_: u8 = 0;
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1613_: u8 = 0;
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: u8 = 0;
    let mut v_reuseFailAlloc_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1620_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1599_ = crate::leanh::lean_ctor_get(v_cfg_1598_, 0);
                v_srcDir_1600_ = crate::leanh::lean_ctor_get(v_cfg_1598_, 1);
                v_roots_1601_ = crate::leanh::lean_ctor_get(v_cfg_1598_, 2);
                v_globs_1602_ = crate::leanh::lean_ctor_get(v_cfg_1598_, 3);
                v_libName_1603_ = crate::leanh::lean_ctor_get(v_cfg_1598_, 4);
                v_libPrefixOnWindows_1604_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1598_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_needs_1605_ = crate::leanh::lean_ctor_get(v_cfg_1598_, 5);
                v_extraDepTargets_1606_ = crate::leanh::lean_ctor_get(v_cfg_1598_, 6);
                v_precompileModules_1607_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1598_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_defaultFacets_1608_ = crate::leanh::lean_ctor_get(v_cfg_1598_, 7);
                v_nativeFacets_1609_ = crate::leanh::lean_ctor_get(v_cfg_1598_, 8);
                v_allowImportAll_1610_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1598_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_1620_ = (!crate::leanh::lean_is_exclusive(v_cfg_1598_)) as u8;
                if v_isSharedCheck_1620_ == 0 {
                    v___x_1612_ = v_cfg_1598_;
                    v_isShared_1613_ = v_isSharedCheck_1620_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1609_);
                    crate::leanh::lean_inc(v_defaultFacets_1608_);
                    crate::leanh::lean_inc(v_extraDepTargets_1606_);
                    crate::leanh::lean_inc(v_needs_1605_);
                    crate::leanh::lean_inc(v_libName_1603_);
                    crate::leanh::lean_inc(v_globs_1602_);
                    crate::leanh::lean_inc(v_roots_1601_);
                    crate::leanh::lean_inc(v_srcDir_1600_);
                    crate::leanh::lean_inc(v_toLeanConfig_1599_);
                    crate::leanh::lean_dec(v_cfg_1598_);
                    v___x_1612_ = crate::leanh::lean_box(0);
                    v_isShared_1613_ = v_isSharedCheck_1620_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1614_ = crate::leanh::lean_box((v_libPrefixOnWindows_1604_) as usize);
                v___x_1615_ = crate::leanh::lean_apply_1(v_f_1597_, v___x_1614_);
                if v_isShared_1613_ == 0 {
                    v___x_1617_ = v___x_1612_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1619_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_toLeanConfig_1599_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_srcDir_1600_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1619_, 2, v_roots_1601_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1619_, 3, v_globs_1602_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1619_, 4, v_libName_1603_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1619_, 5, v_needs_1605_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1619_, 6, v_extraDepTargets_1606_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1619_, 7, v_defaultFacets_1608_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1619_, 8, v_nativeFacets_1609_);
                    v___x_1617_ = v_reuseFailAlloc_1619_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1618_ = (crate::leanh::lean_unbox(v___x_1615_) as u8);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1617_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                    v___x_1618_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1617_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                    v_precompileModules_1607_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1617_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                    v_allowImportAll_1610_,
                );
                return v___x_1617_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__3(
    mut v_x_1621_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1622_: u8 = 0;
    v___x_1622_ = 0;
    return v___x_1622_;
}
pub unsafe fn l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__3___boxed(
    mut v_x_1623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1624_: u8 = 0;
    let mut v_r_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1624_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___lam__3(v_x_1623_);
    crate::leanh::lean_dec_ref(v_x_1623_);
    v_r_1625_ = crate::leanh::lean_box((v_res_1624_) as usize);
    return v_r_1625_;
}
pub unsafe fn l_Lake_LeanLibConfig_libPrefixOnWindows___proj(
    mut v_name_1635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1636_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj___closed__4;
    return v___x_1636_;
}
pub unsafe fn l_Lake_LeanLibConfig_libPrefixOnWindows___proj___boxed(
    mut v_name_1637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1638_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj(v_name_1637_);
    crate::leanh::lean_dec(v_name_1637_);
    return v_res_1638_;
}
pub unsafe fn l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField(
    mut v_name_1639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1640_ = l_Lake_LeanLibConfig_libPrefixOnWindows___proj(v_name_1639_);
    return v___x_1640_;
}
pub unsafe fn l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField___boxed(
    mut v_name_1641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1642_ = l_Lake_LeanLibConfig_libPrefixOnWindows_instConfigField(v_name_1641_);
    crate::leanh::lean_dec(v_name_1641_);
    return v_res_1642_;
}
pub unsafe fn l_Lake_LeanLibConfig_needs___proj___lam__0(
    mut v_cfg_1643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_needs_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_needs_1644_ = crate::leanh::lean_ctor_get(v_cfg_1643_, 5);
    crate::leanh::lean_inc_ref(v_needs_1644_);
    return v_needs_1644_;
}
pub unsafe fn l_Lake_LeanLibConfig_needs___proj___lam__0___boxed(
    mut v_cfg_1645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1646_ = l_Lake_LeanLibConfig_needs___proj___lam__0(v_cfg_1645_);
    crate::leanh::lean_dec_ref(v_cfg_1645_);
    return v_res_1646_;
}
pub unsafe fn l_Lake_LeanLibConfig_needs___proj___lam__1(
    mut v_val_1647_: *mut crate::leanh::LeanObject,
    mut v_cfg_1648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_1654_: u8 = 0;
    let mut v_extraDepTargets_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_1656_: u8 = 0;
    let mut v_defaultFacets_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_1659_: u8 = 0;
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1662_: u8 = 0;
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1666_: u8 = 0;
    let mut v_unused_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1649_ = crate::leanh::lean_ctor_get(v_cfg_1648_, 0);
                v_srcDir_1650_ = crate::leanh::lean_ctor_get(v_cfg_1648_, 1);
                v_roots_1651_ = crate::leanh::lean_ctor_get(v_cfg_1648_, 2);
                v_globs_1652_ = crate::leanh::lean_ctor_get(v_cfg_1648_, 3);
                v_libName_1653_ = crate::leanh::lean_ctor_get(v_cfg_1648_, 4);
                v_libPrefixOnWindows_1654_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1648_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_extraDepTargets_1655_ = crate::leanh::lean_ctor_get(v_cfg_1648_, 6);
                v_precompileModules_1656_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1648_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_defaultFacets_1657_ = crate::leanh::lean_ctor_get(v_cfg_1648_, 7);
                v_nativeFacets_1658_ = crate::leanh::lean_ctor_get(v_cfg_1648_, 8);
                v_allowImportAll_1659_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1648_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_1666_ = (!crate::leanh::lean_is_exclusive(v_cfg_1648_)) as u8;
                if v_isSharedCheck_1666_ == 0 {
                    v_unused_1667_ = crate::leanh::lean_ctor_get(v_cfg_1648_, 5);
                    crate::leanh::lean_dec(v_unused_1667_);
                    v___x_1661_ = v_cfg_1648_;
                    v_isShared_1662_ = v_isSharedCheck_1666_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1658_);
                    crate::leanh::lean_inc(v_defaultFacets_1657_);
                    crate::leanh::lean_inc(v_extraDepTargets_1655_);
                    crate::leanh::lean_inc(v_libName_1653_);
                    crate::leanh::lean_inc(v_globs_1652_);
                    crate::leanh::lean_inc(v_roots_1651_);
                    crate::leanh::lean_inc(v_srcDir_1650_);
                    crate::leanh::lean_inc(v_toLeanConfig_1649_);
                    crate::leanh::lean_dec(v_cfg_1648_);
                    v___x_1661_ = crate::leanh::lean_box(0);
                    v_isShared_1662_ = v_isSharedCheck_1666_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1662_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1661_, 5, v_val_1647_);
                    v___x_1664_ = v___x_1661_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1665_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_toLeanConfig_1649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_srcDir_1650_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1665_, 2, v_roots_1651_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1665_, 3, v_globs_1652_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1665_, 4, v_libName_1653_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1665_, 5, v_val_1647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1665_, 6, v_extraDepTargets_1655_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1665_, 7, v_defaultFacets_1657_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1665_, 8, v_nativeFacets_1658_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1665_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_libPrefixOnWindows_1654_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1665_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                        v_precompileModules_1656_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1665_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                        v_allowImportAll_1659_,
                    );
                    v___x_1664_ = v_reuseFailAlloc_1665_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1664_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_needs___proj___lam__2(
    mut v_f_1668_: *mut crate::leanh::LeanObject,
    mut v_cfg_1669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_1675_: u8 = 0;
    let mut v_needs_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_1678_: u8 = 0;
    let mut v_defaultFacets_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_1681_: u8 = 0;
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1684_: u8 = 0;
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1689_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1670_ = crate::leanh::lean_ctor_get(v_cfg_1669_, 0);
                v_srcDir_1671_ = crate::leanh::lean_ctor_get(v_cfg_1669_, 1);
                v_roots_1672_ = crate::leanh::lean_ctor_get(v_cfg_1669_, 2);
                v_globs_1673_ = crate::leanh::lean_ctor_get(v_cfg_1669_, 3);
                v_libName_1674_ = crate::leanh::lean_ctor_get(v_cfg_1669_, 4);
                v_libPrefixOnWindows_1675_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1669_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_needs_1676_ = crate::leanh::lean_ctor_get(v_cfg_1669_, 5);
                v_extraDepTargets_1677_ = crate::leanh::lean_ctor_get(v_cfg_1669_, 6);
                v_precompileModules_1678_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1669_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_defaultFacets_1679_ = crate::leanh::lean_ctor_get(v_cfg_1669_, 7);
                v_nativeFacets_1680_ = crate::leanh::lean_ctor_get(v_cfg_1669_, 8);
                v_allowImportAll_1681_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1669_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_1689_ = (!crate::leanh::lean_is_exclusive(v_cfg_1669_)) as u8;
                if v_isSharedCheck_1689_ == 0 {
                    v___x_1683_ = v_cfg_1669_;
                    v_isShared_1684_ = v_isSharedCheck_1689_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1680_);
                    crate::leanh::lean_inc(v_defaultFacets_1679_);
                    crate::leanh::lean_inc(v_extraDepTargets_1677_);
                    crate::leanh::lean_inc(v_needs_1676_);
                    crate::leanh::lean_inc(v_libName_1674_);
                    crate::leanh::lean_inc(v_globs_1673_);
                    crate::leanh::lean_inc(v_roots_1672_);
                    crate::leanh::lean_inc(v_srcDir_1671_);
                    crate::leanh::lean_inc(v_toLeanConfig_1670_);
                    crate::leanh::lean_dec(v_cfg_1669_);
                    v___x_1683_ = crate::leanh::lean_box(0);
                    v_isShared_1684_ = v_isSharedCheck_1689_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1685_ = crate::leanh::lean_apply_1(v_f_1668_, v_needs_1676_);
                if v_isShared_1684_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1683_, 5, v___x_1685_);
                    v___x_1687_ = v___x_1683_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1688_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_toLeanConfig_1670_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_srcDir_1671_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1688_, 2, v_roots_1672_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1688_, 3, v_globs_1673_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1688_, 4, v_libName_1674_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1688_, 5, v___x_1685_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1688_, 6, v_extraDepTargets_1677_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1688_, 7, v_defaultFacets_1679_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1688_, 8, v_nativeFacets_1680_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1688_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_libPrefixOnWindows_1675_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1688_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                        v_precompileModules_1678_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1688_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                        v_allowImportAll_1681_,
                    );
                    v___x_1687_ = v_reuseFailAlloc_1688_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1687_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_needs___proj___lam__3(
    mut v_x_1690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1691_ = l_Lake_instInhabitedLeanLibConfig_default___closed__3;
    return v___x_1691_;
}
pub unsafe fn l_Lake_LeanLibConfig_needs___proj___lam__3___boxed(
    mut v_x_1692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_Lake_LeanLibConfig_needs___proj___lam__3(v_x_1692_);
    crate::leanh::lean_dec_ref(v_x_1692_);
    return v_res_1693_;
}
pub unsafe fn l_Lake_LeanLibConfig_needs___proj(
    mut v_name_1703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1704_ = l_Lake_LeanLibConfig_needs___proj___closed__4;
    return v___x_1704_;
}
pub unsafe fn l_Lake_LeanLibConfig_needs___proj___boxed(
    mut v_name_1705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1706_ = l_Lake_LeanLibConfig_needs___proj(v_name_1705_);
    crate::leanh::lean_dec(v_name_1705_);
    return v_res_1706_;
}
pub unsafe fn l_Lake_LeanLibConfig_needs_instConfigField(
    mut v_name_1707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1708_ = l_Lake_LeanLibConfig_needs___proj(v_name_1707_);
    return v___x_1708_;
}
pub unsafe fn l_Lake_LeanLibConfig_needs_instConfigField___boxed(
    mut v_name_1709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1710_ = l_Lake_LeanLibConfig_needs_instConfigField(v_name_1709_);
    crate::leanh::lean_dec(v_name_1709_);
    return v_res_1710_;
}
pub unsafe fn l_Lake_LeanLibConfig_extraDepTargets___proj___lam__0(
    mut v_cfg_1711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_extraDepTargets_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_extraDepTargets_1712_ = crate::leanh::lean_ctor_get(v_cfg_1711_, 6);
    crate::leanh::lean_inc_ref(v_extraDepTargets_1712_);
    return v_extraDepTargets_1712_;
}
pub unsafe fn l_Lake_LeanLibConfig_extraDepTargets___proj___lam__0___boxed(
    mut v_cfg_1713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1714_ = l_Lake_LeanLibConfig_extraDepTargets___proj___lam__0(v_cfg_1713_);
    crate::leanh::lean_dec_ref(v_cfg_1713_);
    return v_res_1714_;
}
pub unsafe fn l_Lake_LeanLibConfig_extraDepTargets___proj___lam__1(
    mut v_val_1715_: *mut crate::leanh::LeanObject,
    mut v_cfg_1716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_1722_: u8 = 0;
    let mut v_needs_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_1724_: u8 = 0;
    let mut v_defaultFacets_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_1727_: u8 = 0;
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1730_: u8 = 0;
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1734_: u8 = 0;
    let mut v_unused_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1717_ = crate::leanh::lean_ctor_get(v_cfg_1716_, 0);
                v_srcDir_1718_ = crate::leanh::lean_ctor_get(v_cfg_1716_, 1);
                v_roots_1719_ = crate::leanh::lean_ctor_get(v_cfg_1716_, 2);
                v_globs_1720_ = crate::leanh::lean_ctor_get(v_cfg_1716_, 3);
                v_libName_1721_ = crate::leanh::lean_ctor_get(v_cfg_1716_, 4);
                v_libPrefixOnWindows_1722_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1716_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_needs_1723_ = crate::leanh::lean_ctor_get(v_cfg_1716_, 5);
                v_precompileModules_1724_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1716_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_defaultFacets_1725_ = crate::leanh::lean_ctor_get(v_cfg_1716_, 7);
                v_nativeFacets_1726_ = crate::leanh::lean_ctor_get(v_cfg_1716_, 8);
                v_allowImportAll_1727_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1716_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_1734_ = (!crate::leanh::lean_is_exclusive(v_cfg_1716_)) as u8;
                if v_isSharedCheck_1734_ == 0 {
                    v_unused_1735_ = crate::leanh::lean_ctor_get(v_cfg_1716_, 6);
                    crate::leanh::lean_dec(v_unused_1735_);
                    v___x_1729_ = v_cfg_1716_;
                    v_isShared_1730_ = v_isSharedCheck_1734_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1726_);
                    crate::leanh::lean_inc(v_defaultFacets_1725_);
                    crate::leanh::lean_inc(v_needs_1723_);
                    crate::leanh::lean_inc(v_libName_1721_);
                    crate::leanh::lean_inc(v_globs_1720_);
                    crate::leanh::lean_inc(v_roots_1719_);
                    crate::leanh::lean_inc(v_srcDir_1718_);
                    crate::leanh::lean_inc(v_toLeanConfig_1717_);
                    crate::leanh::lean_dec(v_cfg_1716_);
                    v___x_1729_ = crate::leanh::lean_box(0);
                    v_isShared_1730_ = v_isSharedCheck_1734_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1730_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1729_, 6, v_val_1715_);
                    v___x_1732_ = v___x_1729_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1733_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_toLeanConfig_1717_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_srcDir_1718_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1733_, 2, v_roots_1719_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1733_, 3, v_globs_1720_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1733_, 4, v_libName_1721_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1733_, 5, v_needs_1723_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1733_, 6, v_val_1715_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1733_, 7, v_defaultFacets_1725_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1733_, 8, v_nativeFacets_1726_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1733_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_libPrefixOnWindows_1722_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1733_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                        v_precompileModules_1724_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1733_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                        v_allowImportAll_1727_,
                    );
                    v___x_1732_ = v_reuseFailAlloc_1733_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1732_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_extraDepTargets___proj___lam__2(
    mut v_f_1736_: *mut crate::leanh::LeanObject,
    mut v_cfg_1737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_1743_: u8 = 0;
    let mut v_needs_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_1746_: u8 = 0;
    let mut v_defaultFacets_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_1749_: u8 = 0;
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1752_: u8 = 0;
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1757_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1738_ = crate::leanh::lean_ctor_get(v_cfg_1737_, 0);
                v_srcDir_1739_ = crate::leanh::lean_ctor_get(v_cfg_1737_, 1);
                v_roots_1740_ = crate::leanh::lean_ctor_get(v_cfg_1737_, 2);
                v_globs_1741_ = crate::leanh::lean_ctor_get(v_cfg_1737_, 3);
                v_libName_1742_ = crate::leanh::lean_ctor_get(v_cfg_1737_, 4);
                v_libPrefixOnWindows_1743_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1737_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_needs_1744_ = crate::leanh::lean_ctor_get(v_cfg_1737_, 5);
                v_extraDepTargets_1745_ = crate::leanh::lean_ctor_get(v_cfg_1737_, 6);
                v_precompileModules_1746_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1737_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_defaultFacets_1747_ = crate::leanh::lean_ctor_get(v_cfg_1737_, 7);
                v_nativeFacets_1748_ = crate::leanh::lean_ctor_get(v_cfg_1737_, 8);
                v_allowImportAll_1749_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1737_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_1757_ = (!crate::leanh::lean_is_exclusive(v_cfg_1737_)) as u8;
                if v_isSharedCheck_1757_ == 0 {
                    v___x_1751_ = v_cfg_1737_;
                    v_isShared_1752_ = v_isSharedCheck_1757_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1748_);
                    crate::leanh::lean_inc(v_defaultFacets_1747_);
                    crate::leanh::lean_inc(v_extraDepTargets_1745_);
                    crate::leanh::lean_inc(v_needs_1744_);
                    crate::leanh::lean_inc(v_libName_1742_);
                    crate::leanh::lean_inc(v_globs_1741_);
                    crate::leanh::lean_inc(v_roots_1740_);
                    crate::leanh::lean_inc(v_srcDir_1739_);
                    crate::leanh::lean_inc(v_toLeanConfig_1738_);
                    crate::leanh::lean_dec(v_cfg_1737_);
                    v___x_1751_ = crate::leanh::lean_box(0);
                    v_isShared_1752_ = v_isSharedCheck_1757_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1753_ = crate::leanh::lean_apply_1(v_f_1736_, v_extraDepTargets_1745_);
                if v_isShared_1752_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1751_, 6, v___x_1753_);
                    v___x_1755_ = v___x_1751_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1756_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_toLeanConfig_1738_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_srcDir_1739_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1756_, 2, v_roots_1740_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1756_, 3, v_globs_1741_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1756_, 4, v_libName_1742_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1756_, 5, v_needs_1744_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1756_, 6, v___x_1753_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1756_, 7, v_defaultFacets_1747_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1756_, 8, v_nativeFacets_1748_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1756_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_libPrefixOnWindows_1743_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1756_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                        v_precompileModules_1746_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1756_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                        v_allowImportAll_1749_,
                    );
                    v___x_1755_ = v_reuseFailAlloc_1756_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1755_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3(
    mut v_x_1760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1761_ = l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3___closed__0;
    return v___x_1761_;
}
pub unsafe fn l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3___boxed(
    mut v_x_1762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1763_ = l_Lake_LeanLibConfig_extraDepTargets___proj___lam__3(v_x_1762_);
    crate::leanh::lean_dec_ref(v_x_1762_);
    return v_res_1763_;
}
pub unsafe fn l_Lake_LeanLibConfig_extraDepTargets___proj(
    mut v_name_1773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1774_ = l_Lake_LeanLibConfig_extraDepTargets___proj___closed__4;
    return v___x_1774_;
}
pub unsafe fn l_Lake_LeanLibConfig_extraDepTargets___proj___boxed(
    mut v_name_1775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1776_ = l_Lake_LeanLibConfig_extraDepTargets___proj(v_name_1775_);
    crate::leanh::lean_dec(v_name_1775_);
    return v_res_1776_;
}
pub unsafe fn l_Lake_LeanLibConfig_extraDepTargets_instConfigField(
    mut v_name_1777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1778_ = l_Lake_LeanLibConfig_extraDepTargets___proj(v_name_1777_);
    return v___x_1778_;
}
pub unsafe fn l_Lake_LeanLibConfig_extraDepTargets_instConfigField___boxed(
    mut v_name_1779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1780_ = l_Lake_LeanLibConfig_extraDepTargets_instConfigField(v_name_1779_);
    crate::leanh::lean_dec(v_name_1779_);
    return v_res_1780_;
}
pub unsafe fn l_Lake_LeanLibConfig_precompileModules___proj___lam__0(
    mut v_cfg_1781_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_precompileModules_1782_: u8 = 0;
    v_precompileModules_1782_ = crate::leanh::lean_ctor_get_uint8(
        v_cfg_1781_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
    );
    return v_precompileModules_1782_;
}
pub unsafe fn l_Lake_LeanLibConfig_precompileModules___proj___lam__0___boxed(
    mut v_cfg_1783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1784_: u8 = 0;
    let mut v_r_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1784_ = l_Lake_LeanLibConfig_precompileModules___proj___lam__0(v_cfg_1783_);
    crate::leanh::lean_dec_ref(v_cfg_1783_);
    v_r_1785_ = crate::leanh::lean_box((v_res_1784_) as usize);
    return v_r_1785_;
}
pub unsafe fn l_Lake_LeanLibConfig_precompileModules___proj___lam__1(
    mut v_val_1786_: u8,
    mut v_cfg_1787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_1793_: u8 = 0;
    let mut v_needs_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defaultFacets_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_1798_: u8 = 0;
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1801_: u8 = 0;
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1805_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1788_ = crate::leanh::lean_ctor_get(v_cfg_1787_, 0);
                v_srcDir_1789_ = crate::leanh::lean_ctor_get(v_cfg_1787_, 1);
                v_roots_1790_ = crate::leanh::lean_ctor_get(v_cfg_1787_, 2);
                v_globs_1791_ = crate::leanh::lean_ctor_get(v_cfg_1787_, 3);
                v_libName_1792_ = crate::leanh::lean_ctor_get(v_cfg_1787_, 4);
                v_libPrefixOnWindows_1793_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1787_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_needs_1794_ = crate::leanh::lean_ctor_get(v_cfg_1787_, 5);
                v_extraDepTargets_1795_ = crate::leanh::lean_ctor_get(v_cfg_1787_, 6);
                v_defaultFacets_1796_ = crate::leanh::lean_ctor_get(v_cfg_1787_, 7);
                v_nativeFacets_1797_ = crate::leanh::lean_ctor_get(v_cfg_1787_, 8);
                v_allowImportAll_1798_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1787_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_1805_ = (!crate::leanh::lean_is_exclusive(v_cfg_1787_)) as u8;
                if v_isSharedCheck_1805_ == 0 {
                    v___x_1800_ = v_cfg_1787_;
                    v_isShared_1801_ = v_isSharedCheck_1805_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1797_);
                    crate::leanh::lean_inc(v_defaultFacets_1796_);
                    crate::leanh::lean_inc(v_extraDepTargets_1795_);
                    crate::leanh::lean_inc(v_needs_1794_);
                    crate::leanh::lean_inc(v_libName_1792_);
                    crate::leanh::lean_inc(v_globs_1791_);
                    crate::leanh::lean_inc(v_roots_1790_);
                    crate::leanh::lean_inc(v_srcDir_1789_);
                    crate::leanh::lean_inc(v_toLeanConfig_1788_);
                    crate::leanh::lean_dec(v_cfg_1787_);
                    v___x_1800_ = crate::leanh::lean_box(0);
                    v_isShared_1801_ = v_isSharedCheck_1805_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1801_ == 0 {
                    v___x_1803_ = v___x_1800_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1804_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_toLeanConfig_1788_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1804_, 1, v_srcDir_1789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1804_, 2, v_roots_1790_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1804_, 3, v_globs_1791_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1804_, 4, v_libName_1792_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1804_, 5, v_needs_1794_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1804_, 6, v_extraDepTargets_1795_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1804_, 7, v_defaultFacets_1796_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1804_, 8, v_nativeFacets_1797_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1804_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_libPrefixOnWindows_1793_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1804_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                        v_allowImportAll_1798_,
                    );
                    v___x_1803_ = v_reuseFailAlloc_1804_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1803_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                    v_val_1786_,
                );
                return v___x_1803_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_precompileModules___proj___lam__1___boxed(
    mut v_val_1806_: *mut crate::leanh::LeanObject,
    mut v_cfg_1807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_71__boxed_1808_: u8 = 0;
    let mut v_res_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_71__boxed_1808_ = (crate::leanh::lean_unbox(v_val_1806_) as u8);
    v_res_1809_ =
        l_Lake_LeanLibConfig_precompileModules___proj___lam__1(v_val_71__boxed_1808_, v_cfg_1807_);
    return v_res_1809_;
}
pub unsafe fn l_Lake_LeanLibConfig_precompileModules___proj___lam__2(
    mut v_f_1810_: *mut crate::leanh::LeanObject,
    mut v_cfg_1811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_1817_: u8 = 0;
    let mut v_needs_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_1820_: u8 = 0;
    let mut v_defaultFacets_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_1823_: u8 = 0;
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1826_: u8 = 0;
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: u8 = 0;
    let mut v_reuseFailAlloc_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1833_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1812_ = crate::leanh::lean_ctor_get(v_cfg_1811_, 0);
                v_srcDir_1813_ = crate::leanh::lean_ctor_get(v_cfg_1811_, 1);
                v_roots_1814_ = crate::leanh::lean_ctor_get(v_cfg_1811_, 2);
                v_globs_1815_ = crate::leanh::lean_ctor_get(v_cfg_1811_, 3);
                v_libName_1816_ = crate::leanh::lean_ctor_get(v_cfg_1811_, 4);
                v_libPrefixOnWindows_1817_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1811_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_needs_1818_ = crate::leanh::lean_ctor_get(v_cfg_1811_, 5);
                v_extraDepTargets_1819_ = crate::leanh::lean_ctor_get(v_cfg_1811_, 6);
                v_precompileModules_1820_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1811_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_defaultFacets_1821_ = crate::leanh::lean_ctor_get(v_cfg_1811_, 7);
                v_nativeFacets_1822_ = crate::leanh::lean_ctor_get(v_cfg_1811_, 8);
                v_allowImportAll_1823_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1811_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_1833_ = (!crate::leanh::lean_is_exclusive(v_cfg_1811_)) as u8;
                if v_isSharedCheck_1833_ == 0 {
                    v___x_1825_ = v_cfg_1811_;
                    v_isShared_1826_ = v_isSharedCheck_1833_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1822_);
                    crate::leanh::lean_inc(v_defaultFacets_1821_);
                    crate::leanh::lean_inc(v_extraDepTargets_1819_);
                    crate::leanh::lean_inc(v_needs_1818_);
                    crate::leanh::lean_inc(v_libName_1816_);
                    crate::leanh::lean_inc(v_globs_1815_);
                    crate::leanh::lean_inc(v_roots_1814_);
                    crate::leanh::lean_inc(v_srcDir_1813_);
                    crate::leanh::lean_inc(v_toLeanConfig_1812_);
                    crate::leanh::lean_dec(v_cfg_1811_);
                    v___x_1825_ = crate::leanh::lean_box(0);
                    v_isShared_1826_ = v_isSharedCheck_1833_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1827_ = crate::leanh::lean_box((v_precompileModules_1820_) as usize);
                v___x_1828_ = crate::leanh::lean_apply_1(v_f_1810_, v___x_1827_);
                if v_isShared_1826_ == 0 {
                    v___x_1830_ = v___x_1825_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1832_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_toLeanConfig_1812_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1832_, 1, v_srcDir_1813_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1832_, 2, v_roots_1814_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1832_, 3, v_globs_1815_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1832_, 4, v_libName_1816_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1832_, 5, v_needs_1818_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1832_, 6, v_extraDepTargets_1819_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1832_, 7, v_defaultFacets_1821_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1832_, 8, v_nativeFacets_1822_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1832_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_libPrefixOnWindows_1817_,
                    );
                    v___x_1830_ = v_reuseFailAlloc_1832_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1831_ = (crate::leanh::lean_unbox(v___x_1828_) as u8);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1830_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                    v___x_1831_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1830_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                    v_allowImportAll_1823_,
                );
                return v___x_1830_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_precompileModules___proj(
    mut v_name_1842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1843_ = l_Lake_LeanLibConfig_precompileModules___proj___closed__3;
    return v___x_1843_;
}
pub unsafe fn l_Lake_LeanLibConfig_precompileModules___proj___boxed(
    mut v_name_1844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1845_ = l_Lake_LeanLibConfig_precompileModules___proj(v_name_1844_);
    crate::leanh::lean_dec(v_name_1844_);
    return v_res_1845_;
}
pub unsafe fn l_Lake_LeanLibConfig_precompileModules_instConfigField(
    mut v_name_1846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1847_ = l_Lake_LeanLibConfig_precompileModules___proj(v_name_1846_);
    return v___x_1847_;
}
pub unsafe fn l_Lake_LeanLibConfig_precompileModules_instConfigField___boxed(
    mut v_name_1848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1849_ = l_Lake_LeanLibConfig_precompileModules_instConfigField(v_name_1848_);
    crate::leanh::lean_dec(v_name_1848_);
    return v_res_1849_;
}
pub unsafe fn l_Lake_LeanLibConfig_defaultFacets___proj___lam__0(
    mut v_cfg_1850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defaultFacets_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_defaultFacets_1851_ = crate::leanh::lean_ctor_get(v_cfg_1850_, 7);
    crate::leanh::lean_inc_ref(v_defaultFacets_1851_);
    return v_defaultFacets_1851_;
}
pub unsafe fn l_Lake_LeanLibConfig_defaultFacets___proj___lam__0___boxed(
    mut v_cfg_1852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1853_ = l_Lake_LeanLibConfig_defaultFacets___proj___lam__0(v_cfg_1852_);
    crate::leanh::lean_dec_ref(v_cfg_1852_);
    return v_res_1853_;
}
pub unsafe fn l_Lake_LeanLibConfig_defaultFacets___proj___lam__1(
    mut v_val_1854_: *mut crate::leanh::LeanObject,
    mut v_cfg_1855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_1861_: u8 = 0;
    let mut v_needs_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_1864_: u8 = 0;
    let mut v_nativeFacets_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_1866_: u8 = 0;
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1869_: u8 = 0;
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1873_: u8 = 0;
    let mut v_unused_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1856_ = crate::leanh::lean_ctor_get(v_cfg_1855_, 0);
                v_srcDir_1857_ = crate::leanh::lean_ctor_get(v_cfg_1855_, 1);
                v_roots_1858_ = crate::leanh::lean_ctor_get(v_cfg_1855_, 2);
                v_globs_1859_ = crate::leanh::lean_ctor_get(v_cfg_1855_, 3);
                v_libName_1860_ = crate::leanh::lean_ctor_get(v_cfg_1855_, 4);
                v_libPrefixOnWindows_1861_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1855_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_needs_1862_ = crate::leanh::lean_ctor_get(v_cfg_1855_, 5);
                v_extraDepTargets_1863_ = crate::leanh::lean_ctor_get(v_cfg_1855_, 6);
                v_precompileModules_1864_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1855_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_nativeFacets_1865_ = crate::leanh::lean_ctor_get(v_cfg_1855_, 8);
                v_allowImportAll_1866_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1855_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_1873_ = (!crate::leanh::lean_is_exclusive(v_cfg_1855_)) as u8;
                if v_isSharedCheck_1873_ == 0 {
                    v_unused_1874_ = crate::leanh::lean_ctor_get(v_cfg_1855_, 7);
                    crate::leanh::lean_dec(v_unused_1874_);
                    v___x_1868_ = v_cfg_1855_;
                    v_isShared_1869_ = v_isSharedCheck_1873_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1865_);
                    crate::leanh::lean_inc(v_extraDepTargets_1863_);
                    crate::leanh::lean_inc(v_needs_1862_);
                    crate::leanh::lean_inc(v_libName_1860_);
                    crate::leanh::lean_inc(v_globs_1859_);
                    crate::leanh::lean_inc(v_roots_1858_);
                    crate::leanh::lean_inc(v_srcDir_1857_);
                    crate::leanh::lean_inc(v_toLeanConfig_1856_);
                    crate::leanh::lean_dec(v_cfg_1855_);
                    v___x_1868_ = crate::leanh::lean_box(0);
                    v_isShared_1869_ = v_isSharedCheck_1873_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1869_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1868_, 7, v_val_1854_);
                    v___x_1871_ = v___x_1868_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1872_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_toLeanConfig_1856_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_srcDir_1857_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 2, v_roots_1858_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 3, v_globs_1859_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 4, v_libName_1860_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 5, v_needs_1862_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 6, v_extraDepTargets_1863_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 7, v_val_1854_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 8, v_nativeFacets_1865_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1872_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_libPrefixOnWindows_1861_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1872_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                        v_precompileModules_1864_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1872_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                        v_allowImportAll_1866_,
                    );
                    v___x_1871_ = v_reuseFailAlloc_1872_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1871_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_defaultFacets___proj___lam__2(
    mut v_f_1875_: *mut crate::leanh::LeanObject,
    mut v_cfg_1876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_1882_: u8 = 0;
    let mut v_needs_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_1885_: u8 = 0;
    let mut v_defaultFacets_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_1888_: u8 = 0;
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1891_: u8 = 0;
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1896_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1877_ = crate::leanh::lean_ctor_get(v_cfg_1876_, 0);
                v_srcDir_1878_ = crate::leanh::lean_ctor_get(v_cfg_1876_, 1);
                v_roots_1879_ = crate::leanh::lean_ctor_get(v_cfg_1876_, 2);
                v_globs_1880_ = crate::leanh::lean_ctor_get(v_cfg_1876_, 3);
                v_libName_1881_ = crate::leanh::lean_ctor_get(v_cfg_1876_, 4);
                v_libPrefixOnWindows_1882_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1876_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_needs_1883_ = crate::leanh::lean_ctor_get(v_cfg_1876_, 5);
                v_extraDepTargets_1884_ = crate::leanh::lean_ctor_get(v_cfg_1876_, 6);
                v_precompileModules_1885_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1876_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_defaultFacets_1886_ = crate::leanh::lean_ctor_get(v_cfg_1876_, 7);
                v_nativeFacets_1887_ = crate::leanh::lean_ctor_get(v_cfg_1876_, 8);
                v_allowImportAll_1888_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1876_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_1896_ = (!crate::leanh::lean_is_exclusive(v_cfg_1876_)) as u8;
                if v_isSharedCheck_1896_ == 0 {
                    v___x_1890_ = v_cfg_1876_;
                    v_isShared_1891_ = v_isSharedCheck_1896_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1887_);
                    crate::leanh::lean_inc(v_defaultFacets_1886_);
                    crate::leanh::lean_inc(v_extraDepTargets_1884_);
                    crate::leanh::lean_inc(v_needs_1883_);
                    crate::leanh::lean_inc(v_libName_1881_);
                    crate::leanh::lean_inc(v_globs_1880_);
                    crate::leanh::lean_inc(v_roots_1879_);
                    crate::leanh::lean_inc(v_srcDir_1878_);
                    crate::leanh::lean_inc(v_toLeanConfig_1877_);
                    crate::leanh::lean_dec(v_cfg_1876_);
                    v___x_1890_ = crate::leanh::lean_box(0);
                    v_isShared_1891_ = v_isSharedCheck_1896_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1892_ = crate::leanh::lean_apply_1(v_f_1875_, v_defaultFacets_1886_);
                if v_isShared_1891_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1890_, 7, v___x_1892_);
                    v___x_1894_ = v___x_1890_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1895_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_toLeanConfig_1877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_srcDir_1878_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1895_, 2, v_roots_1879_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1895_, 3, v_globs_1880_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1895_, 4, v_libName_1881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1895_, 5, v_needs_1883_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1895_, 6, v_extraDepTargets_1884_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1895_, 7, v___x_1892_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1895_, 8, v_nativeFacets_1887_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1895_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_libPrefixOnWindows_1882_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1895_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                        v_precompileModules_1885_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1895_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                        v_allowImportAll_1888_,
                    );
                    v___x_1894_ = v_reuseFailAlloc_1895_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1894_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_defaultFacets___proj___lam__3(
    mut v_x_1897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1898_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1899_ = lean_mk_empty_array_with_capacity(v___x_1898_);
    crate::leanh::lean_dec_ref(v___x_1899_);
    v___x_1900_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanLibConfig_default___closed__4),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanLibConfig_default___closed__4_once),
        _init_l_Lake_instInhabitedLeanLibConfig_default___closed__4,
    );
    return v___x_1900_;
}
pub unsafe fn l_Lake_LeanLibConfig_defaultFacets___proj___lam__3___boxed(
    mut v_x_1901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1902_ = l_Lake_LeanLibConfig_defaultFacets___proj___lam__3(v_x_1901_);
    crate::leanh::lean_dec_ref(v_x_1901_);
    return v_res_1902_;
}
pub unsafe fn l_Lake_LeanLibConfig_defaultFacets___proj(
    mut v_name_1912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1913_ = l_Lake_LeanLibConfig_defaultFacets___proj___closed__4;
    return v___x_1913_;
}
pub unsafe fn l_Lake_LeanLibConfig_defaultFacets___proj___boxed(
    mut v_name_1914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1915_ = l_Lake_LeanLibConfig_defaultFacets___proj(v_name_1914_);
    crate::leanh::lean_dec(v_name_1914_);
    return v_res_1915_;
}
pub unsafe fn l_Lake_LeanLibConfig_defaultFacets_instConfigField(
    mut v_name_1916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1917_ = l_Lake_LeanLibConfig_defaultFacets___proj(v_name_1916_);
    return v___x_1917_;
}
pub unsafe fn l_Lake_LeanLibConfig_defaultFacets_instConfigField___boxed(
    mut v_name_1918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1919_ = l_Lake_LeanLibConfig_defaultFacets_instConfigField(v_name_1918_);
    crate::leanh::lean_dec(v_name_1918_);
    return v_res_1919_;
}
pub unsafe fn l_Lake_LeanLibConfig_nativeFacets___proj___lam__0(
    mut v_cfg_1920_: *mut crate::leanh::LeanObject,
    mut v___y_1921_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_nativeFacets_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nativeFacets_1922_ = crate::leanh::lean_ctor_get(v_cfg_1920_, 8);
    crate::leanh::lean_inc_ref(v_nativeFacets_1922_);
    crate::leanh::lean_dec_ref(v_cfg_1920_);
    v___x_1923_ = crate::leanh::lean_box((v___y_1921_) as usize);
    v___x_1924_ = crate::leanh::lean_apply_1(v_nativeFacets_1922_, v___x_1923_);
    return v___x_1924_;
}
pub unsafe fn l_Lake_LeanLibConfig_nativeFacets___proj___lam__0___boxed(
    mut v_cfg_1925_: *mut crate::leanh::LeanObject,
    mut v___y_1926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_147__boxed_1927_: u8 = 0;
    let mut v_res_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_147__boxed_1927_ = (crate::leanh::lean_unbox(v___y_1926_) as u8);
    v_res_1928_ =
        l_Lake_LeanLibConfig_nativeFacets___proj___lam__0(v_cfg_1925_, v___y_147__boxed_1927_);
    return v_res_1928_;
}
pub unsafe fn l_Lake_LeanLibConfig_nativeFacets___proj___lam__1(
    mut v_val_1929_: *mut crate::leanh::LeanObject,
    mut v_cfg_1930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_1936_: u8 = 0;
    let mut v_needs_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_1939_: u8 = 0;
    let mut v_defaultFacets_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_1941_: u8 = 0;
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1944_: u8 = 0;
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1948_: u8 = 0;
    let mut v_unused_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1931_ = crate::leanh::lean_ctor_get(v_cfg_1930_, 0);
                v_srcDir_1932_ = crate::leanh::lean_ctor_get(v_cfg_1930_, 1);
                v_roots_1933_ = crate::leanh::lean_ctor_get(v_cfg_1930_, 2);
                v_globs_1934_ = crate::leanh::lean_ctor_get(v_cfg_1930_, 3);
                v_libName_1935_ = crate::leanh::lean_ctor_get(v_cfg_1930_, 4);
                v_libPrefixOnWindows_1936_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1930_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_needs_1937_ = crate::leanh::lean_ctor_get(v_cfg_1930_, 5);
                v_extraDepTargets_1938_ = crate::leanh::lean_ctor_get(v_cfg_1930_, 6);
                v_precompileModules_1939_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1930_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_defaultFacets_1940_ = crate::leanh::lean_ctor_get(v_cfg_1930_, 7);
                v_allowImportAll_1941_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1930_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_1948_ = (!crate::leanh::lean_is_exclusive(v_cfg_1930_)) as u8;
                if v_isSharedCheck_1948_ == 0 {
                    v_unused_1949_ = crate::leanh::lean_ctor_get(v_cfg_1930_, 8);
                    crate::leanh::lean_dec(v_unused_1949_);
                    v___x_1943_ = v_cfg_1930_;
                    v_isShared_1944_ = v_isSharedCheck_1948_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_defaultFacets_1940_);
                    crate::leanh::lean_inc(v_extraDepTargets_1938_);
                    crate::leanh::lean_inc(v_needs_1937_);
                    crate::leanh::lean_inc(v_libName_1935_);
                    crate::leanh::lean_inc(v_globs_1934_);
                    crate::leanh::lean_inc(v_roots_1933_);
                    crate::leanh::lean_inc(v_srcDir_1932_);
                    crate::leanh::lean_inc(v_toLeanConfig_1931_);
                    crate::leanh::lean_dec(v_cfg_1930_);
                    v___x_1943_ = crate::leanh::lean_box(0);
                    v_isShared_1944_ = v_isSharedCheck_1948_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1944_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1943_, 8, v_val_1929_);
                    v___x_1946_ = v___x_1943_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1947_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_toLeanConfig_1931_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_srcDir_1932_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 2, v_roots_1933_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 3, v_globs_1934_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 4, v_libName_1935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 5, v_needs_1937_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 6, v_extraDepTargets_1938_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 7, v_defaultFacets_1940_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 8, v_val_1929_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1947_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_libPrefixOnWindows_1936_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1947_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                        v_precompileModules_1939_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1947_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                        v_allowImportAll_1941_,
                    );
                    v___x_1946_ = v_reuseFailAlloc_1947_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1946_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_nativeFacets___proj___lam__2(
    mut v_f_1950_: *mut crate::leanh::LeanObject,
    mut v_cfg_1951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_1957_: u8 = 0;
    let mut v_needs_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_1960_: u8 = 0;
    let mut v_defaultFacets_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_1963_: u8 = 0;
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1966_: u8 = 0;
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1952_ = crate::leanh::lean_ctor_get(v_cfg_1951_, 0);
                v_srcDir_1953_ = crate::leanh::lean_ctor_get(v_cfg_1951_, 1);
                v_roots_1954_ = crate::leanh::lean_ctor_get(v_cfg_1951_, 2);
                v_globs_1955_ = crate::leanh::lean_ctor_get(v_cfg_1951_, 3);
                v_libName_1956_ = crate::leanh::lean_ctor_get(v_cfg_1951_, 4);
                v_libPrefixOnWindows_1957_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1951_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_needs_1958_ = crate::leanh::lean_ctor_get(v_cfg_1951_, 5);
                v_extraDepTargets_1959_ = crate::leanh::lean_ctor_get(v_cfg_1951_, 6);
                v_precompileModules_1960_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1951_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_defaultFacets_1961_ = crate::leanh::lean_ctor_get(v_cfg_1951_, 7);
                v_nativeFacets_1962_ = crate::leanh::lean_ctor_get(v_cfg_1951_, 8);
                v_allowImportAll_1963_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1951_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_1971_ = (!crate::leanh::lean_is_exclusive(v_cfg_1951_)) as u8;
                if v_isSharedCheck_1971_ == 0 {
                    v___x_1965_ = v_cfg_1951_;
                    v_isShared_1966_ = v_isSharedCheck_1971_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1962_);
                    crate::leanh::lean_inc(v_defaultFacets_1961_);
                    crate::leanh::lean_inc(v_extraDepTargets_1959_);
                    crate::leanh::lean_inc(v_needs_1958_);
                    crate::leanh::lean_inc(v_libName_1956_);
                    crate::leanh::lean_inc(v_globs_1955_);
                    crate::leanh::lean_inc(v_roots_1954_);
                    crate::leanh::lean_inc(v_srcDir_1953_);
                    crate::leanh::lean_inc(v_toLeanConfig_1952_);
                    crate::leanh::lean_dec(v_cfg_1951_);
                    v___x_1965_ = crate::leanh::lean_box(0);
                    v_isShared_1966_ = v_isSharedCheck_1971_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1967_ = crate::leanh::lean_apply_1(v_f_1950_, v_nativeFacets_1962_);
                if v_isShared_1966_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1965_, 8, v___x_1967_);
                    v___x_1969_ = v___x_1965_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1970_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_toLeanConfig_1952_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_srcDir_1953_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1970_, 2, v_roots_1954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1970_, 3, v_globs_1955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1970_, 4, v_libName_1956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1970_, 5, v_needs_1958_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1970_, 6, v_extraDepTargets_1959_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1970_, 7, v_defaultFacets_1961_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1970_, 8, v___x_1967_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1970_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_libPrefixOnWindows_1957_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1970_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                        v_precompileModules_1960_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1970_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                        v_allowImportAll_1963_,
                    );
                    v___x_1969_ = v_reuseFailAlloc_1970_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1969_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_nativeFacets___proj___lam__3(
    mut v_x_1972_: *mut crate::leanh::LeanObject,
    mut v___y_1973_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_1973_ == 0 {
                    v___x_1979_ = l_Lake_Module_oFacet;
                    v___y_1975_ = v___x_1979_;
                    state = 1;
                    continue;
                } else {
                    v___x_1980_ = l_Lake_Module_oExportFacet;
                    v___y_1975_ = v___x_1980_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1976_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1977_ = lean_mk_empty_array_with_capacity(v___x_1976_);
                crate::leanh::lean_inc(v___y_1975_);
                v___x_1978_ = lean_array_push(v___x_1977_, v___y_1975_);
                return v___x_1978_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_nativeFacets___proj___lam__3___boxed(
    mut v_x_1981_: *mut crate::leanh::LeanObject,
    mut v___y_1982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_197__boxed_1983_: u8 = 0;
    let mut v_res_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_197__boxed_1983_ = (crate::leanh::lean_unbox(v___y_1982_) as u8);
    v_res_1984_ =
        l_Lake_LeanLibConfig_nativeFacets___proj___lam__3(v_x_1981_, v___y_197__boxed_1983_);
    crate::leanh::lean_dec_ref(v_x_1981_);
    return v_res_1984_;
}
pub unsafe fn l_Lake_LeanLibConfig_nativeFacets___proj(
    mut v_name_1994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1995_ = l_Lake_LeanLibConfig_nativeFacets___proj___closed__4;
    return v___x_1995_;
}
pub unsafe fn l_Lake_LeanLibConfig_nativeFacets___proj___boxed(
    mut v_name_1996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1997_ = l_Lake_LeanLibConfig_nativeFacets___proj(v_name_1996_);
    crate::leanh::lean_dec(v_name_1996_);
    return v_res_1997_;
}
pub unsafe fn l_Lake_LeanLibConfig_nativeFacets_instConfigField(
    mut v_name_1998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1999_ = l_Lake_LeanLibConfig_nativeFacets___proj(v_name_1998_);
    return v___x_1999_;
}
pub unsafe fn l_Lake_LeanLibConfig_nativeFacets_instConfigField___boxed(
    mut v_name_2000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2001_ = l_Lake_LeanLibConfig_nativeFacets_instConfigField(v_name_2000_);
    crate::leanh::lean_dec(v_name_2000_);
    return v_res_2001_;
}
pub unsafe fn l_Lake_LeanLibConfig_allowImportAll___proj___lam__0(
    mut v_cfg_2002_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_allowImportAll_2003_: u8 = 0;
    v_allowImportAll_2003_ = crate::leanh::lean_ctor_get_uint8(
        v_cfg_2002_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
    );
    return v_allowImportAll_2003_;
}
pub unsafe fn l_Lake_LeanLibConfig_allowImportAll___proj___lam__0___boxed(
    mut v_cfg_2004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2005_: u8 = 0;
    let mut v_r_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2005_ = l_Lake_LeanLibConfig_allowImportAll___proj___lam__0(v_cfg_2004_);
    crate::leanh::lean_dec_ref(v_cfg_2004_);
    v_r_2006_ = crate::leanh::lean_box((v_res_2005_) as usize);
    return v_r_2006_;
}
pub unsafe fn l_Lake_LeanLibConfig_allowImportAll___proj___lam__1(
    mut v_val_2007_: u8,
    mut v_cfg_2008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_2014_: u8 = 0;
    let mut v_needs_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_2017_: u8 = 0;
    let mut v_defaultFacets_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2022_: u8 = 0;
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2026_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_2009_ = crate::leanh::lean_ctor_get(v_cfg_2008_, 0);
                v_srcDir_2010_ = crate::leanh::lean_ctor_get(v_cfg_2008_, 1);
                v_roots_2011_ = crate::leanh::lean_ctor_get(v_cfg_2008_, 2);
                v_globs_2012_ = crate::leanh::lean_ctor_get(v_cfg_2008_, 3);
                v_libName_2013_ = crate::leanh::lean_ctor_get(v_cfg_2008_, 4);
                v_libPrefixOnWindows_2014_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_2008_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_needs_2015_ = crate::leanh::lean_ctor_get(v_cfg_2008_, 5);
                v_extraDepTargets_2016_ = crate::leanh::lean_ctor_get(v_cfg_2008_, 6);
                v_precompileModules_2017_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_2008_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_defaultFacets_2018_ = crate::leanh::lean_ctor_get(v_cfg_2008_, 7);
                v_nativeFacets_2019_ = crate::leanh::lean_ctor_get(v_cfg_2008_, 8);
                v_isSharedCheck_2026_ = (!crate::leanh::lean_is_exclusive(v_cfg_2008_)) as u8;
                if v_isSharedCheck_2026_ == 0 {
                    v___x_2021_ = v_cfg_2008_;
                    v_isShared_2022_ = v_isSharedCheck_2026_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_2019_);
                    crate::leanh::lean_inc(v_defaultFacets_2018_);
                    crate::leanh::lean_inc(v_extraDepTargets_2016_);
                    crate::leanh::lean_inc(v_needs_2015_);
                    crate::leanh::lean_inc(v_libName_2013_);
                    crate::leanh::lean_inc(v_globs_2012_);
                    crate::leanh::lean_inc(v_roots_2011_);
                    crate::leanh::lean_inc(v_srcDir_2010_);
                    crate::leanh::lean_inc(v_toLeanConfig_2009_);
                    crate::leanh::lean_dec(v_cfg_2008_);
                    v___x_2021_ = crate::leanh::lean_box(0);
                    v_isShared_2022_ = v_isSharedCheck_2026_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2022_ == 0 {
                    v___x_2024_ = v___x_2021_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2025_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_toLeanConfig_2009_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_srcDir_2010_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_roots_2011_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2025_, 3, v_globs_2012_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2025_, 4, v_libName_2013_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2025_, 5, v_needs_2015_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2025_, 6, v_extraDepTargets_2016_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2025_, 7, v_defaultFacets_2018_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2025_, 8, v_nativeFacets_2019_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2025_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_libPrefixOnWindows_2014_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2025_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                        v_precompileModules_2017_,
                    );
                    v___x_2024_ = v_reuseFailAlloc_2025_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2024_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                    v_val_2007_,
                );
                return v___x_2024_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_allowImportAll___proj___lam__1___boxed(
    mut v_val_2027_: *mut crate::leanh::LeanObject,
    mut v_cfg_2028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_71__boxed_2029_: u8 = 0;
    let mut v_res_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_71__boxed_2029_ = (crate::leanh::lean_unbox(v_val_2027_) as u8);
    v_res_2030_ =
        l_Lake_LeanLibConfig_allowImportAll___proj___lam__1(v_val_71__boxed_2029_, v_cfg_2028_);
    return v_res_2030_;
}
pub unsafe fn l_Lake_LeanLibConfig_allowImportAll___proj___lam__2(
    mut v_f_2031_: *mut crate::leanh::LeanObject,
    mut v_cfg_2032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_2038_: u8 = 0;
    let mut v_needs_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_2041_: u8 = 0;
    let mut v_defaultFacets_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_2044_: u8 = 0;
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2047_: u8 = 0;
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: u8 = 0;
    let mut v_reuseFailAlloc_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2054_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_2033_ = crate::leanh::lean_ctor_get(v_cfg_2032_, 0);
                v_srcDir_2034_ = crate::leanh::lean_ctor_get(v_cfg_2032_, 1);
                v_roots_2035_ = crate::leanh::lean_ctor_get(v_cfg_2032_, 2);
                v_globs_2036_ = crate::leanh::lean_ctor_get(v_cfg_2032_, 3);
                v_libName_2037_ = crate::leanh::lean_ctor_get(v_cfg_2032_, 4);
                v_libPrefixOnWindows_2038_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_2032_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_needs_2039_ = crate::leanh::lean_ctor_get(v_cfg_2032_, 5);
                v_extraDepTargets_2040_ = crate::leanh::lean_ctor_get(v_cfg_2032_, 6);
                v_precompileModules_2041_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_2032_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_defaultFacets_2042_ = crate::leanh::lean_ctor_get(v_cfg_2032_, 7);
                v_nativeFacets_2043_ = crate::leanh::lean_ctor_get(v_cfg_2032_, 8);
                v_allowImportAll_2044_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_2032_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_2054_ = (!crate::leanh::lean_is_exclusive(v_cfg_2032_)) as u8;
                if v_isSharedCheck_2054_ == 0 {
                    v___x_2046_ = v_cfg_2032_;
                    v_isShared_2047_ = v_isSharedCheck_2054_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_2043_);
                    crate::leanh::lean_inc(v_defaultFacets_2042_);
                    crate::leanh::lean_inc(v_extraDepTargets_2040_);
                    crate::leanh::lean_inc(v_needs_2039_);
                    crate::leanh::lean_inc(v_libName_2037_);
                    crate::leanh::lean_inc(v_globs_2036_);
                    crate::leanh::lean_inc(v_roots_2035_);
                    crate::leanh::lean_inc(v_srcDir_2034_);
                    crate::leanh::lean_inc(v_toLeanConfig_2033_);
                    crate::leanh::lean_dec(v_cfg_2032_);
                    v___x_2046_ = crate::leanh::lean_box(0);
                    v_isShared_2047_ = v_isSharedCheck_2054_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2048_ = crate::leanh::lean_box((v_allowImportAll_2044_) as usize);
                v___x_2049_ = crate::leanh::lean_apply_1(v_f_2031_, v___x_2048_);
                if v_isShared_2047_ == 0 {
                    v___x_2051_ = v___x_2046_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2053_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_toLeanConfig_2033_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_srcDir_2034_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2053_, 2, v_roots_2035_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2053_, 3, v_globs_2036_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2053_, 4, v_libName_2037_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2053_, 5, v_needs_2039_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2053_, 6, v_extraDepTargets_2040_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2053_, 7, v_defaultFacets_2042_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2053_, 8, v_nativeFacets_2043_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2053_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_libPrefixOnWindows_2038_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2053_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                        v_precompileModules_2041_,
                    );
                    v___x_2051_ = v_reuseFailAlloc_2053_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2052_ = (crate::leanh::lean_unbox(v___x_2049_) as u8);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2051_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                    v___x_2052_,
                );
                return v___x_2051_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_allowImportAll___proj(
    mut v_name_2063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2064_ = l_Lake_LeanLibConfig_allowImportAll___proj___closed__3;
    return v___x_2064_;
}
pub unsafe fn l_Lake_LeanLibConfig_allowImportAll___proj___boxed(
    mut v_name_2065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2066_ = l_Lake_LeanLibConfig_allowImportAll___proj(v_name_2065_);
    crate::leanh::lean_dec(v_name_2065_);
    return v_res_2066_;
}
pub unsafe fn l_Lake_LeanLibConfig_allowImportAll_instConfigField(
    mut v_name_2067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2068_ = l_Lake_LeanLibConfig_allowImportAll___proj(v_name_2067_);
    return v___x_2068_;
}
pub unsafe fn l_Lake_LeanLibConfig_allowImportAll_instConfigField___boxed(
    mut v_name_2069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2070_ = l_Lake_LeanLibConfig_allowImportAll_instConfigField(v_name_2069_);
    crate::leanh::lean_dec(v_name_2069_);
    return v_res_2070_;
}
pub unsafe fn l_Lake_LeanLibConfig_toLeanConfig___proj___lam__0(
    mut v_cfg_2071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toLeanConfig_2072_ = crate::leanh::lean_ctor_get(v_cfg_2071_, 0);
    crate::leanh::lean_inc_ref(v_toLeanConfig_2072_);
    return v_toLeanConfig_2072_;
}
pub unsafe fn l_Lake_LeanLibConfig_toLeanConfig___proj___lam__0___boxed(
    mut v_cfg_2073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2074_ = l_Lake_LeanLibConfig_toLeanConfig___proj___lam__0(v_cfg_2073_);
    crate::leanh::lean_dec_ref(v_cfg_2073_);
    return v_res_2074_;
}
pub unsafe fn l_Lake_LeanLibConfig_toLeanConfig___proj___lam__1(
    mut v_val_2075_: *mut crate::leanh::LeanObject,
    mut v_cfg_2076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_srcDir_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_2081_: u8 = 0;
    let mut v_needs_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_2084_: u8 = 0;
    let mut v_defaultFacets_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_2087_: u8 = 0;
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2090_: u8 = 0;
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2094_: u8 = 0;
    let mut v_unused_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_srcDir_2077_ = crate::leanh::lean_ctor_get(v_cfg_2076_, 1);
                v_roots_2078_ = crate::leanh::lean_ctor_get(v_cfg_2076_, 2);
                v_globs_2079_ = crate::leanh::lean_ctor_get(v_cfg_2076_, 3);
                v_libName_2080_ = crate::leanh::lean_ctor_get(v_cfg_2076_, 4);
                v_libPrefixOnWindows_2081_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_2076_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_needs_2082_ = crate::leanh::lean_ctor_get(v_cfg_2076_, 5);
                v_extraDepTargets_2083_ = crate::leanh::lean_ctor_get(v_cfg_2076_, 6);
                v_precompileModules_2084_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_2076_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_defaultFacets_2085_ = crate::leanh::lean_ctor_get(v_cfg_2076_, 7);
                v_nativeFacets_2086_ = crate::leanh::lean_ctor_get(v_cfg_2076_, 8);
                v_allowImportAll_2087_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_2076_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_2094_ = (!crate::leanh::lean_is_exclusive(v_cfg_2076_)) as u8;
                if v_isSharedCheck_2094_ == 0 {
                    v_unused_2095_ = crate::leanh::lean_ctor_get(v_cfg_2076_, 0);
                    crate::leanh::lean_dec(v_unused_2095_);
                    v___x_2089_ = v_cfg_2076_;
                    v_isShared_2090_ = v_isSharedCheck_2094_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_2086_);
                    crate::leanh::lean_inc(v_defaultFacets_2085_);
                    crate::leanh::lean_inc(v_extraDepTargets_2083_);
                    crate::leanh::lean_inc(v_needs_2082_);
                    crate::leanh::lean_inc(v_libName_2080_);
                    crate::leanh::lean_inc(v_globs_2079_);
                    crate::leanh::lean_inc(v_roots_2078_);
                    crate::leanh::lean_inc(v_srcDir_2077_);
                    crate::leanh::lean_dec(v_cfg_2076_);
                    v___x_2089_ = crate::leanh::lean_box(0);
                    v_isShared_2090_ = v_isSharedCheck_2094_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2090_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2089_, 0, v_val_2075_);
                    v___x_2092_ = v___x_2089_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2093_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_val_2075_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_srcDir_2077_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 2, v_roots_2078_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 3, v_globs_2079_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 4, v_libName_2080_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 5, v_needs_2082_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 6, v_extraDepTargets_2083_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 7, v_defaultFacets_2085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2093_, 8, v_nativeFacets_2086_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2093_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_libPrefixOnWindows_2081_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2093_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                        v_precompileModules_2084_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2093_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                        v_allowImportAll_2087_,
                    );
                    v___x_2092_ = v_reuseFailAlloc_2093_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2092_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_toLeanConfig___proj___lam__2(
    mut v_f_2096_: *mut crate::leanh::LeanObject,
    mut v_cfg_2097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libName_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_2103_: u8 = 0;
    let mut v_needs_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_2106_: u8 = 0;
    let mut v_defaultFacets_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_2109_: u8 = 0;
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2112_: u8 = 0;
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2117_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_2098_ = crate::leanh::lean_ctor_get(v_cfg_2097_, 0);
                v_srcDir_2099_ = crate::leanh::lean_ctor_get(v_cfg_2097_, 1);
                v_roots_2100_ = crate::leanh::lean_ctor_get(v_cfg_2097_, 2);
                v_globs_2101_ = crate::leanh::lean_ctor_get(v_cfg_2097_, 3);
                v_libName_2102_ = crate::leanh::lean_ctor_get(v_cfg_2097_, 4);
                v_libPrefixOnWindows_2103_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_2097_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_needs_2104_ = crate::leanh::lean_ctor_get(v_cfg_2097_, 5);
                v_extraDepTargets_2105_ = crate::leanh::lean_ctor_get(v_cfg_2097_, 6);
                v_precompileModules_2106_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_2097_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                );
                v_defaultFacets_2107_ = crate::leanh::lean_ctor_get(v_cfg_2097_, 7);
                v_nativeFacets_2108_ = crate::leanh::lean_ctor_get(v_cfg_2097_, 8);
                v_allowImportAll_2109_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_2097_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                );
                v_isSharedCheck_2117_ = (!crate::leanh::lean_is_exclusive(v_cfg_2097_)) as u8;
                if v_isSharedCheck_2117_ == 0 {
                    v___x_2111_ = v_cfg_2097_;
                    v_isShared_2112_ = v_isSharedCheck_2117_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_2108_);
                    crate::leanh::lean_inc(v_defaultFacets_2107_);
                    crate::leanh::lean_inc(v_extraDepTargets_2105_);
                    crate::leanh::lean_inc(v_needs_2104_);
                    crate::leanh::lean_inc(v_libName_2102_);
                    crate::leanh::lean_inc(v_globs_2101_);
                    crate::leanh::lean_inc(v_roots_2100_);
                    crate::leanh::lean_inc(v_srcDir_2099_);
                    crate::leanh::lean_inc(v_toLeanConfig_2098_);
                    crate::leanh::lean_dec(v_cfg_2097_);
                    v___x_2111_ = crate::leanh::lean_box(0);
                    v_isShared_2112_ = v_isSharedCheck_2117_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2113_ = crate::leanh::lean_apply_1(v_f_2096_, v_toLeanConfig_2098_);
                if v_isShared_2112_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2111_, 0, v___x_2113_);
                    v___x_2115_ = v___x_2111_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2116_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2113_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_srcDir_2099_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2116_, 2, v_roots_2100_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2116_, 3, v_globs_2101_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2116_, 4, v_libName_2102_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2116_, 5, v_needs_2104_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2116_, 6, v_extraDepTargets_2105_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2116_, 7, v_defaultFacets_2107_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2116_, 8, v_nativeFacets_2108_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2116_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_libPrefixOnWindows_2103_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2116_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
                        v_precompileModules_2106_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2116_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
                        v_allowImportAll_2109_,
                    );
                    v___x_2115_ = v_reuseFailAlloc_2116_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2115_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3(
    mut v_x_2125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2126_ = l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__1;
    return v___x_2126_;
}
pub unsafe fn l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___boxed(
    mut v_x_2127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2128_ = l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3(v_x_2127_);
    crate::leanh::lean_dec_ref(v_x_2127_);
    return v_res_2128_;
}
pub unsafe fn l_Lake_LeanLibConfig_toLeanConfig___proj(
    mut v_name_2138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2139_ = l_Lake_LeanLibConfig_toLeanConfig___proj___closed__4;
    return v___x_2139_;
}
pub unsafe fn l_Lake_LeanLibConfig_toLeanConfig___proj___boxed(
    mut v_name_2140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2141_ = l_Lake_LeanLibConfig_toLeanConfig___proj(v_name_2140_);
    crate::leanh::lean_dec(v_name_2140_);
    return v_res_2141_;
}
pub unsafe fn l_Lake_LeanLibConfig_toLeanConfig_instConfigParent(
    mut v_name_2142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2143_ = l_Lake_LeanLibConfig_toLeanConfig___proj(v_name_2142_);
    return v___x_2143_;
}
pub unsafe fn l_Lake_LeanLibConfig_toLeanConfig_instConfigParent___boxed(
    mut v_name_2144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2145_ = l_Lake_LeanLibConfig_toLeanConfig_instConfigParent(v_name_2144_);
    crate::leanh::lean_dec(v_name_2144_);
    return v_res_2145_;
}
pub unsafe fn _init_l_Lake_LeanLibConfig___fields___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2155_ = l_Lake_LeanLibConfig___fields___closed__3;
    v___x_2156_ = l_Lake_LeanLibConfig___fields___closed__0;
    v___x_2157_ = lean_array_push(v___x_2156_, v___x_2155_);
    return v___x_2157_;
}
pub unsafe fn _init_l_Lake_LeanLibConfig___fields___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2165_ = l_Lake_LeanLibConfig___fields___closed__7;
    v___x_2166_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__4),
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__4_once),
        _init_l_Lake_LeanLibConfig___fields___closed__4,
    );
    v___x_2167_ = lean_array_push(v___x_2166_, v___x_2165_);
    return v___x_2167_;
}
pub unsafe fn _init_l_Lake_LeanLibConfig___fields___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2175_ = l_Lake_LeanLibConfig___fields___closed__11;
    v___x_2176_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__8),
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__8_once),
        _init_l_Lake_LeanLibConfig___fields___closed__8,
    );
    v___x_2177_ = lean_array_push(v___x_2176_, v___x_2175_);
    return v___x_2177_;
}
pub unsafe fn _init_l_Lake_LeanLibConfig___fields___closed__16() -> *mut crate::leanh::LeanObject {
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2185_ = l_Lake_LeanLibConfig___fields___closed__15;
    v___x_2186_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__12),
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__12_once),
        _init_l_Lake_LeanLibConfig___fields___closed__12,
    );
    v___x_2187_ = lean_array_push(v___x_2186_, v___x_2185_);
    return v___x_2187_;
}
pub unsafe fn _init_l_Lake_LeanLibConfig___fields___closed__20() -> *mut crate::leanh::LeanObject {
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2195_ = l_Lake_LeanLibConfig___fields___closed__19;
    v___x_2196_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__16),
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__16_once),
        _init_l_Lake_LeanLibConfig___fields___closed__16,
    );
    v___x_2197_ = lean_array_push(v___x_2196_, v___x_2195_);
    return v___x_2197_;
}
pub unsafe fn _init_l_Lake_LeanLibConfig___fields___closed__24() -> *mut crate::leanh::LeanObject {
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2205_ = l_Lake_LeanLibConfig___fields___closed__23;
    v___x_2206_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__20),
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__20_once),
        _init_l_Lake_LeanLibConfig___fields___closed__20,
    );
    v___x_2207_ = lean_array_push(v___x_2206_, v___x_2205_);
    return v___x_2207_;
}
pub unsafe fn _init_l_Lake_LeanLibConfig___fields___closed__28() -> *mut crate::leanh::LeanObject {
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2215_ = l_Lake_LeanLibConfig___fields___closed__27;
    v___x_2216_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__24),
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__24_once),
        _init_l_Lake_LeanLibConfig___fields___closed__24,
    );
    v___x_2217_ = lean_array_push(v___x_2216_, v___x_2215_);
    return v___x_2217_;
}
pub unsafe fn _init_l_Lake_LeanLibConfig___fields___closed__32() -> *mut crate::leanh::LeanObject {
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2225_ = l_Lake_LeanLibConfig___fields___closed__31;
    v___x_2226_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__28),
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__28_once),
        _init_l_Lake_LeanLibConfig___fields___closed__28,
    );
    v___x_2227_ = lean_array_push(v___x_2226_, v___x_2225_);
    return v___x_2227_;
}
pub unsafe fn _init_l_Lake_LeanLibConfig___fields___closed__36() -> *mut crate::leanh::LeanObject {
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2235_ = l_Lake_LeanLibConfig___fields___closed__35;
    v___x_2236_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__32),
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__32_once),
        _init_l_Lake_LeanLibConfig___fields___closed__32,
    );
    v___x_2237_ = lean_array_push(v___x_2236_, v___x_2235_);
    return v___x_2237_;
}
pub unsafe fn _init_l_Lake_LeanLibConfig___fields___closed__40() -> *mut crate::leanh::LeanObject {
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2245_ = l_Lake_LeanLibConfig___fields___closed__39;
    v___x_2246_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__36),
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__36_once),
        _init_l_Lake_LeanLibConfig___fields___closed__36,
    );
    v___x_2247_ = lean_array_push(v___x_2246_, v___x_2245_);
    return v___x_2247_;
}
pub unsafe fn _init_l_Lake_LeanLibConfig___fields___closed__44() -> *mut crate::leanh::LeanObject {
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2255_ = l_Lake_LeanLibConfig___fields___closed__43;
    v___x_2256_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__40),
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__40_once),
        _init_l_Lake_LeanLibConfig___fields___closed__40,
    );
    v___x_2257_ = lean_array_push(v___x_2256_, v___x_2255_);
    return v___x_2257_;
}
pub unsafe fn _init_l_Lake_LeanLibConfig___fields___closed__45() -> *mut crate::leanh::LeanObject {
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2258_ = l_Lake_LeanConfig___fields;
    v___x_2259_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__44),
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__44_once),
        _init_l_Lake_LeanLibConfig___fields___closed__44,
    );
    v___x_2260_ = l_Array_append___redArg(v___x_2259_, v___x_2258_);
    return v___x_2260_;
}
pub unsafe fn _init_l_Lake_LeanLibConfig___fields___closed__49() -> *mut crate::leanh::LeanObject {
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2268_ = l_Lake_LeanLibConfig___fields___closed__48;
    v___x_2269_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__45),
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__45_once),
        _init_l_Lake_LeanLibConfig___fields___closed__45,
    );
    v___x_2270_ = lean_array_push(v___x_2269_, v___x_2268_);
    return v___x_2270_;
}
pub unsafe fn _init_l_Lake_LeanLibConfig___fields() -> *mut crate::leanh::LeanObject {
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2271_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__49),
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig___fields___closed__49_once),
        _init_l_Lake_LeanLibConfig___fields___closed__49,
    );
    return v___x_2271_;
}
pub unsafe fn l_Lake_LeanLibConfig_instConfigFields(
    mut v_name_2272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2273_ = l_Lake_LeanLibConfig___fields;
    return v___x_2273_;
}
pub unsafe fn l_Lake_LeanLibConfig_instConfigFields___boxed(
    mut v_name_2274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2275_ = l_Lake_LeanLibConfig_instConfigFields(v_name_2274_);
    crate::leanh::lean_dec(v_name_2274_);
    return v_res_2275_;
}
pub unsafe fn l_Lake_LeanLibConfig_instConfigInfo___lam__0(
    mut v_x1_2276_: *mut crate::leanh::LeanObject,
    mut v_x2_2277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2278_ = crate::leanh::lean_ctor_get(v_x2_2277_, 0);
    crate::leanh::lean_inc(v_name_2278_);
    v___x_2279_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_name_2278_,
        v_x2_2277_,
        v_x1_2276_,
    );
    return v___x_2279_;
}
pub unsafe fn _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2280_ = l_Lake_LeanLibConfig___fields;
    v___x_2281_ = lean_array_get_size(v___x_2280_);
    return v___x_2281_;
}
pub unsafe fn _init_l_Lake_LeanLibConfig_instConfigInfo___closed__11() -> u8 {
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: u8 = 0;
    v___x_2301_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0,
    );
    v___x_2302_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2303_ = lean_nat_dec_lt(v___x_2302_, v___x_2301_);
    return v___x_2303_;
}
pub unsafe fn _init_l_Lake_LeanLibConfig_instConfigInfo___closed__13() -> u8 {
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: u8 = 0;
    v___x_2305_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0,
    );
    v___x_2306_ = lean_nat_dec_le(v___x_2305_, v___x_2305_);
    return v___x_2306_;
}
pub unsafe fn _init_l_Lake_LeanLibConfig_instConfigInfo___closed__14() -> usize {
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: usize = 0;
    v___x_2307_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_LeanLibConfig_instConfigInfo___closed__0,
    );
    v___x_2308_ = lean_usize_of_nat(v___x_2307_);
    return v___x_2308_;
}
pub unsafe fn _init_l_Lake_LeanLibConfig_instConfigInfo___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: usize = 0;
    let mut v___x_2311_: usize = 0;
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2309_ = crate::leanh::lean_box(1);
    v___x_2310_ = crate::leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig_instConfigInfo___closed__14),
        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig_instConfigInfo___closed__14_once),
        _init_l_Lake_LeanLibConfig_instConfigInfo___closed__14,
    );
    v___x_2311_ = 0usize;
    v___x_2312_ = l_Lake_LeanLibConfig___fields;
    v___f_2313_ = l_Lake_LeanLibConfig_instConfigInfo___closed__12;
    v___x_2314_ = l_Lake_LeanLibConfig_instConfigInfo___closed__10;
    v___x_2315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2314_,
        v___f_2313_,
        v___x_2312_,
        v___x_2311_,
        v___x_2310_,
        v___x_2309_,
    );
    return v___x_2315_;
}
pub unsafe fn _init_l_Lake_LeanLibConfig_instConfigInfo() -> *mut crate::leanh::LeanObject {
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: u8 = 0;
    let mut v___x_2323_: u8 = 0;
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2316_ = l_Lake_LeanLibConfig___fields;
                v___x_2321_ = crate::leanh::lean_box(1);
                v___x_2322_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Lake_LeanLibConfig_instConfigInfo___closed__11),
                    core::ptr::addr_of_mut!(l_Lake_LeanLibConfig_instConfigInfo___closed__11_once),
                    _init_l_Lake_LeanLibConfig_instConfigInfo___closed__11,
                );
                if v___x_2322_ == 0 {
                    v___y_2318_ = v___x_2321_;
                    state = 1;
                    continue;
                } else {
                    v___x_2323_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Lake_LeanLibConfig_instConfigInfo___closed__13),
                        core::ptr::addr_of_mut!(
                            l_Lake_LeanLibConfig_instConfigInfo___closed__13_once
                        ),
                        _init_l_Lake_LeanLibConfig_instConfigInfo___closed__13,
                    );
                    if v___x_2323_ == 0 {
                        if v___x_2322_ == 0 {
                            v___y_2318_ = v___x_2321_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2324_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lake_LeanLibConfig_instConfigInfo___closed__15
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lake_LeanLibConfig_instConfigInfo___closed__15_once
                                ),
                                _init_l_Lake_LeanLibConfig_instConfigInfo___closed__15,
                            );
                            v___y_2318_ = v___x_2324_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_2325_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lake_LeanLibConfig_instConfigInfo___closed__15
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lake_LeanLibConfig_instConfigInfo___closed__15_once
                            ),
                            _init_l_Lake_LeanLibConfig_instConfigInfo___closed__15,
                        );
                        v___y_2318_ = v___x_2325_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2319_ = crate::leanh::lean_unsigned_to_nat(1);
                crate::leanh::lean_inc(v___y_2318_);
                v___x_2320_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2320_, 0, v___x_2316_);
                crate::leanh::lean_ctor_set(v___x_2320_, 1, v___y_2318_);
                crate::leanh::lean_ctor_set(v___x_2320_, 2, v___x_2319_);
                return v___x_2320_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_instEmptyCollection___lam__0(
    mut v_x_2326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2327_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2327_, 0, v_x_2326_);
    return v___x_2327_;
}
pub unsafe fn l_Lake_LeanLibConfig_instEmptyCollection(
    mut v_name_2329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2339_: usize = 0;
    let mut v___x_2340_: usize = 0;
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: u8 = 0;
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2330_ = l_Lake_LeanLibConfig_instEmptyCollection___closed__0;
    v___f_2331_ = l_Lake_instInhabitedLeanLibConfig_default___closed__0;
    v___x_2332_ = l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__0;
    v___x_2333_ = l_Lake_LeanLibConfig_toLeanConfig___proj___lam__3___closed__1;
    v___x_2334_ = l_Lake_instInhabitedLeanLibConfig_default___closed__1;
    v___x_2335_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2336_ = lean_mk_empty_array_with_capacity(v___x_2335_);
    v___x_2337_ = lean_array_push(v___x_2336_, v_name_2329_);
    v___x_2338_ = l_Lake_LeanLibConfig_instConfigInfo___closed__10;
    v_sz_2339_ = lean_array_size(v___x_2337_);
    v___x_2340_ = 0usize;
    crate::leanh::lean_inc_ref(v___x_2337_);
    v___x_2341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2338_,
        v___f_2330_,
        v_sz_2339_,
        v___x_2340_,
        v___x_2337_,
    );
    v___x_2342_ = l_Lake_instInhabitedLeanLibConfig_default___closed__2;
    v___x_2343_ = 0;
    v___x_2344_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanLibConfig_default___closed__4),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanLibConfig_default___closed__4_once),
        _init_l_Lake_instInhabitedLeanLibConfig_default___closed__4,
    );
    v___x_2345_ = crate::leanh::lean_alloc_ctor(0, 9, (3) as u32);
    crate::leanh::lean_ctor_set(v___x_2345_, 0, v___x_2333_);
    crate::leanh::lean_ctor_set(v___x_2345_, 1, v___x_2334_);
    crate::leanh::lean_ctor_set(v___x_2345_, 2, v___x_2337_);
    crate::leanh::lean_ctor_set(v___x_2345_, 3, v___x_2341_);
    crate::leanh::lean_ctor_set(v___x_2345_, 4, v___x_2342_);
    crate::leanh::lean_ctor_set(v___x_2345_, 5, v___x_2332_);
    crate::leanh::lean_ctor_set(v___x_2345_, 6, v___x_2332_);
    crate::leanh::lean_ctor_set(v___x_2345_, 7, v___x_2344_);
    crate::leanh::lean_ctor_set(v___x_2345_, 8, v___f_2331_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2345_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
        v___x_2343_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2345_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
        v___x_2343_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2345_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
        v___x_2343_,
    );
    return v___x_2345_;
}
pub unsafe fn l_Lake_LeanLibConfig_name___redArg(
    mut v_n_2346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_n_2346_);
    return v_n_2346_;
}
pub unsafe fn l_Lake_LeanLibConfig_name___redArg___boxed(
    mut v_n_2347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2348_ = l_Lake_LeanLibConfig_name___redArg(v_n_2347_);
    crate::leanh::lean_dec(v_n_2347_);
    return v_res_2348_;
}
pub unsafe fn l_Lake_LeanLibConfig_name(
    mut v_n_2349_: *mut crate::leanh::LeanObject,
    mut v_x_2350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_n_2349_);
    return v_n_2349_;
}
pub unsafe fn l_Lake_LeanLibConfig_name___boxed(
    mut v_n_2351_: *mut crate::leanh::LeanObject,
    mut v_x_2352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2353_ = l_Lake_LeanLibConfig_name(v_n_2351_, v_x_2352_);
    crate::leanh::lean_dec_ref(v_x_2352_);
    crate::leanh::lean_dec(v_n_2351_);
    return v_res_2353_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(
    mut v_mod_2354_: *mut crate::leanh::LeanObject,
    mut v_as_2355_: *mut crate::leanh::LeanObject,
    mut v_i_2356_: usize,
    mut v_stop_2357_: usize,
) -> u8 {
    let mut v___x_2358_: u8 = 0;
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: u8 = 0;
    let mut v___x_2361_: usize = 0;
    let mut v___x_2362_: usize = 0;
    let mut v___x_2364_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2358_ = lean_usize_dec_eq(v_i_2356_, v_stop_2357_);
                if v___x_2358_ == 0 {
                    v___x_2359_ = lean_array_uget_borrowed(v_as_2355_, v_i_2356_);
                    v___x_2360_ = l_Lake_Glob_matches(v_mod_2354_, v___x_2359_);
                    if v___x_2360_ == 0 {
                        v___x_2361_ = 1usize;
                        v___x_2362_ = lean_usize_add(v_i_2356_, v___x_2361_);
                        v_i_2356_ = v___x_2362_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2360_;
                    }
                } else {
                    v___x_2364_ = 0;
                    return v___x_2364_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0___boxed(
    mut v_mod_2365_: *mut crate::leanh::LeanObject,
    mut v_as_2366_: *mut crate::leanh::LeanObject,
    mut v_i_2367_: *mut crate::leanh::LeanObject,
    mut v_stop_2368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2369_: usize = 0;
    let mut v_stop_boxed_2370_: usize = 0;
    let mut v_res_2371_: u8 = 0;
    let mut v_r_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2369_ = crate::leanh::lean_unbox_usize(v_i_2367_);
    crate::leanh::lean_dec(v_i_2367_);
    v_stop_boxed_2370_ = crate::leanh::lean_unbox_usize(v_stop_2368_);
    crate::leanh::lean_dec(v_stop_2368_);
    v_res_2371_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v_mod_2365_, v_as_2366_, v_i_boxed_2369_, v_stop_boxed_2370_);
    crate::leanh::lean_dec_ref(v_as_2366_);
    crate::leanh::lean_dec(v_mod_2365_);
    v_r_2372_ = crate::leanh::lean_box((v_res_2371_) as usize);
    return v_r_2372_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1(
    mut v_mod_2373_: *mut crate::leanh::LeanObject,
    mut v_as_2374_: *mut crate::leanh::LeanObject,
    mut v_i_2375_: usize,
    mut v_stop_2376_: usize,
) -> u8 {
    let mut v___x_2377_: u8 = 0;
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: u8 = 0;
    let mut v___x_2380_: usize = 0;
    let mut v___x_2381_: usize = 0;
    let mut v___x_2383_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2377_ = lean_usize_dec_eq(v_i_2375_, v_stop_2376_);
                if v___x_2377_ == 0 {
                    v___x_2378_ = lean_array_uget_borrowed(v_as_2374_, v_i_2375_);
                    v___x_2379_ = l_Lean_Name_isPrefixOf(v___x_2378_, v_mod_2373_);
                    if v___x_2379_ == 0 {
                        v___x_2380_ = 1usize;
                        v___x_2381_ = lean_usize_add(v_i_2375_, v___x_2380_);
                        v_i_2375_ = v___x_2381_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2379_;
                    }
                } else {
                    v___x_2383_ = 0;
                    return v___x_2383_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1___boxed(
    mut v_mod_2384_: *mut crate::leanh::LeanObject,
    mut v_as_2385_: *mut crate::leanh::LeanObject,
    mut v_i_2386_: *mut crate::leanh::LeanObject,
    mut v_stop_2387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2388_: usize = 0;
    let mut v_stop_boxed_2389_: usize = 0;
    let mut v_res_2390_: u8 = 0;
    let mut v_r_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2388_ = crate::leanh::lean_unbox_usize(v_i_2386_);
    crate::leanh::lean_dec(v_i_2386_);
    v_stop_boxed_2389_ = crate::leanh::lean_unbox_usize(v_stop_2387_);
    crate::leanh::lean_dec(v_stop_2387_);
    v_res_2390_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1(v_mod_2384_, v_as_2385_, v_i_boxed_2388_, v_stop_boxed_2389_);
    crate::leanh::lean_dec_ref(v_as_2385_);
    crate::leanh::lean_dec(v_mod_2384_);
    v_r_2391_ = crate::leanh::lean_box((v_res_2390_) as usize);
    return v_r_2391_;
}
pub unsafe fn l_Lake_LeanLibConfig_isLocalModule___redArg(
    mut v_mod_2392_: *mut crate::leanh::LeanObject,
    mut v_self_2393_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_roots_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: u8 = 0;
    let mut v___x_2400_: usize = 0;
    let mut v___x_2401_: usize = 0;
    let mut v___x_2402_: u8 = 0;
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: u8 = 0;
    let mut v___x_2406_: usize = 0;
    let mut v___x_2407_: usize = 0;
    let mut v___x_2408_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_roots_2394_ = crate::leanh::lean_ctor_get(v_self_2393_, 2);
                v_globs_2395_ = crate::leanh::lean_ctor_get(v_self_2393_, 3);
                v___x_2403_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2404_ = lean_array_get_size(v_roots_2394_);
                v___x_2405_ = lean_nat_dec_lt(v___x_2403_, v___x_2404_);
                if v___x_2405_ == 0 {
                    state = 1;
                    continue;
                } else {
                    if v___x_2405_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_2406_ = 0usize;
                        v___x_2407_ = lean_usize_of_nat(v___x_2404_);
                        v___x_2408_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__1(v_mod_2392_, v_roots_2394_, v___x_2406_, v___x_2407_);
                        if v___x_2408_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            return v___x_2408_;
                        }
                    }
                }
            }
            1 => {
                v___x_2397_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2398_ = lean_array_get_size(v_globs_2395_);
                v___x_2399_ = lean_nat_dec_lt(v___x_2397_, v___x_2398_);
                if v___x_2399_ == 0 {
                    return v___x_2399_;
                } else {
                    if v___x_2399_ == 0 {
                        return v___x_2399_;
                    } else {
                        v___x_2400_ = 0usize;
                        v___x_2401_ = lean_usize_of_nat(v___x_2398_);
                        v___x_2402_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v_mod_2392_, v_globs_2395_, v___x_2400_, v___x_2401_);
                        return v___x_2402_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_isLocalModule___redArg___boxed(
    mut v_mod_2409_: *mut crate::leanh::LeanObject,
    mut v_self_2410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2411_: u8 = 0;
    let mut v_r_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2411_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_2409_, v_self_2410_);
    crate::leanh::lean_dec_ref(v_self_2410_);
    crate::leanh::lean_dec(v_mod_2409_);
    v_r_2412_ = crate::leanh::lean_box((v_res_2411_) as usize);
    return v_r_2412_;
}
pub unsafe fn l_Lake_LeanLibConfig_isLocalModule(
    mut v_n_2413_: *mut crate::leanh::LeanObject,
    mut v_mod_2414_: *mut crate::leanh::LeanObject,
    mut v_self_2415_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2416_: u8 = 0;
    v___x_2416_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_2414_, v_self_2415_);
    return v___x_2416_;
}
pub unsafe fn l_Lake_LeanLibConfig_isLocalModule___boxed(
    mut v_n_2417_: *mut crate::leanh::LeanObject,
    mut v_mod_2418_: *mut crate::leanh::LeanObject,
    mut v_self_2419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2420_: u8 = 0;
    let mut v_r_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2420_ = l_Lake_LeanLibConfig_isLocalModule(v_n_2417_, v_mod_2418_, v_self_2419_);
    crate::leanh::lean_dec_ref(v_self_2419_);
    crate::leanh::lean_dec(v_mod_2418_);
    crate::leanh::lean_dec(v_n_2417_);
    v_r_2421_ = crate::leanh::lean_box((v_res_2420_) as usize);
    return v_r_2421_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0(
    mut v_mod_2422_: *mut crate::leanh::LeanObject,
    mut v_self_2423_: *mut crate::leanh::LeanObject,
    mut v_as_2424_: *mut crate::leanh::LeanObject,
    mut v_i_2425_: usize,
    mut v_stop_2426_: usize,
) -> u8 {
    let mut v___x_2427_: u8 = 0;
    let mut v___x_2428_: u8 = 0;
    let mut v___y_2430_: u8 = 0;
    let mut v___x_2431_: usize = 0;
    let mut v___x_2432_: usize = 0;
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: u8 = 0;
    let mut v_globs_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: u8 = 0;
    let mut v___x_2440_: usize = 0;
    let mut v___x_2441_: usize = 0;
    let mut v___x_2442_: u8 = 0;
    let mut v___x_2443_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2427_ = lean_usize_dec_eq(v_i_2425_, v_stop_2426_);
                if v___x_2427_ == 0 {
                    v___x_2428_ = 1;
                    v___x_2434_ = lean_array_uget_borrowed(v_as_2424_, v_i_2425_);
                    v___x_2435_ = l_Lean_Name_isPrefixOf(v___x_2434_, v_mod_2422_);
                    if v___x_2435_ == 0 {
                        v___y_2430_ = v___x_2435_;
                        state = 1;
                        continue;
                    } else {
                        v_globs_2436_ = crate::leanh::lean_ctor_get(v_self_2423_, 3);
                        v___x_2437_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2438_ = lean_array_get_size(v_globs_2436_);
                        v___x_2439_ = lean_nat_dec_lt(v___x_2437_, v___x_2438_);
                        if v___x_2439_ == 0 {
                            v___y_2430_ = v___x_2427_;
                            state = 1;
                            continue;
                        } else {
                            if v___x_2439_ == 0 {
                                v___y_2430_ = v___x_2427_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2440_ = 0usize;
                                v___x_2441_ = lean_usize_of_nat(v___x_2438_);
                                v___x_2442_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v___x_2434_, v_globs_2436_, v___x_2440_, v___x_2441_);
                                v___y_2430_ = v___x_2442_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_2443_ = 0;
                    return v___x_2443_;
                }
            }
            1 => {
                if v___y_2430_ == 0 {
                    v___x_2431_ = 1usize;
                    v___x_2432_ = lean_usize_add(v_i_2425_, v___x_2431_);
                    v_i_2425_ = v___x_2432_;
                    state = 0;
                    continue;
                } else {
                    return v___x_2428_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0___boxed(
    mut v_mod_2444_: *mut crate::leanh::LeanObject,
    mut v_self_2445_: *mut crate::leanh::LeanObject,
    mut v_as_2446_: *mut crate::leanh::LeanObject,
    mut v_i_2447_: *mut crate::leanh::LeanObject,
    mut v_stop_2448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2449_: usize = 0;
    let mut v_stop_boxed_2450_: usize = 0;
    let mut v_res_2451_: u8 = 0;
    let mut v_r_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2449_ = crate::leanh::lean_unbox_usize(v_i_2447_);
    crate::leanh::lean_dec(v_i_2447_);
    v_stop_boxed_2450_ = crate::leanh::lean_unbox_usize(v_stop_2448_);
    crate::leanh::lean_dec(v_stop_2448_);
    v_res_2451_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0(v_mod_2444_, v_self_2445_, v_as_2446_, v_i_boxed_2449_, v_stop_boxed_2450_);
    crate::leanh::lean_dec_ref(v_as_2446_);
    crate::leanh::lean_dec_ref(v_self_2445_);
    crate::leanh::lean_dec(v_mod_2444_);
    v_r_2452_ = crate::leanh::lean_box((v_res_2451_) as usize);
    return v_r_2452_;
}
pub unsafe fn l_Lake_LeanLibConfig_isBuildableModule___redArg(
    mut v_mod_2453_: *mut crate::leanh::LeanObject,
    mut v_self_2454_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_roots_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: u8 = 0;
    let mut v___x_2461_: usize = 0;
    let mut v___x_2462_: usize = 0;
    let mut v___x_2463_: u8 = 0;
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: u8 = 0;
    let mut v___x_2467_: usize = 0;
    let mut v___x_2468_: usize = 0;
    let mut v___x_2469_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_roots_2455_ = crate::leanh::lean_ctor_get(v_self_2454_, 2);
                v_globs_2456_ = crate::leanh::lean_ctor_get(v_self_2454_, 3);
                v___x_2464_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2465_ = lean_array_get_size(v_globs_2456_);
                v___x_2466_ = lean_nat_dec_lt(v___x_2464_, v___x_2465_);
                if v___x_2466_ == 0 {
                    state = 1;
                    continue;
                } else {
                    if v___x_2466_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_2467_ = 0usize;
                        v___x_2468_ = lean_usize_of_nat(v___x_2465_);
                        v___x_2469_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isLocalModule_spec__0(v_mod_2453_, v_globs_2456_, v___x_2467_, v___x_2468_);
                        if v___x_2469_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            return v___x_2469_;
                        }
                    }
                }
            }
            1 => {
                v___x_2458_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2459_ = lean_array_get_size(v_roots_2455_);
                v___x_2460_ = lean_nat_dec_lt(v___x_2458_, v___x_2459_);
                if v___x_2460_ == 0 {
                    return v___x_2460_;
                } else {
                    if v___x_2460_ == 0 {
                        return v___x_2460_;
                    } else {
                        v___x_2461_ = 0usize;
                        v___x_2462_ = lean_usize_of_nat(v___x_2459_);
                        v___x_2463_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_LeanLibConfig_isBuildableModule_spec__0(v_mod_2453_, v_self_2454_, v_roots_2455_, v___x_2461_, v___x_2462_);
                        return v___x_2463_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLibConfig_isBuildableModule___redArg___boxed(
    mut v_mod_2470_: *mut crate::leanh::LeanObject,
    mut v_self_2471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2472_: u8 = 0;
    let mut v_r_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2472_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_2470_, v_self_2471_);
    crate::leanh::lean_dec_ref(v_self_2471_);
    crate::leanh::lean_dec(v_mod_2470_);
    v_r_2473_ = crate::leanh::lean_box((v_res_2472_) as usize);
    return v_r_2473_;
}
pub unsafe fn l_Lake_LeanLibConfig_isBuildableModule(
    mut v_n_2474_: *mut crate::leanh::LeanObject,
    mut v_mod_2475_: *mut crate::leanh::LeanObject,
    mut v_self_2476_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2477_: u8 = 0;
    v___x_2477_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_2475_, v_self_2476_);
    return v___x_2477_;
}
pub unsafe fn l_Lake_LeanLibConfig_isBuildableModule___boxed(
    mut v_n_2478_: *mut crate::leanh::LeanObject,
    mut v_mod_2479_: *mut crate::leanh::LeanObject,
    mut v_self_2480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2481_: u8 = 0;
    let mut v_r_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2481_ = l_Lake_LeanLibConfig_isBuildableModule(v_n_2478_, v_mod_2479_, v_self_2480_);
    crate::leanh::lean_dec_ref(v_self_2480_);
    crate::leanh::lean_dec(v_mod_2479_);
    crate::leanh::lean_dec(v_n_2478_);
    v_r_2482_ = crate::leanh::lean_box((v_res_2481_) as usize);
    return v_r_2482_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_LeanLibConfig(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_NameMangling(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Casing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Facets(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Glob(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lake_LeanLibConfig___fields = _init_l_Lake_LeanLibConfig___fields();
    crate::leanh::lean_mark_persistent(l_Lake_LeanLibConfig___fields);
    l_Lake_LeanLibConfig_instConfigInfo = _init_l_Lake_LeanLibConfig_instConfigInfo();
    crate::leanh::lean_mark_persistent(l_Lake_LeanLibConfig_instConfigInfo);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_LeanLibConfig(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lake_Config_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_LeanLibConfig(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_NameMangling(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Casing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Facets(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_LeanConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Glob(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanLibConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_LeanLibConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Config_LeanLibConfig(builtin);
}
