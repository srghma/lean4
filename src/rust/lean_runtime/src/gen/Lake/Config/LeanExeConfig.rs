// Lean compiler output
// Module: Lake.Config.LeanExeConfig
// Imports: Lake.Build.Facets Lake.Config.LeanConfig Lake.Config.Meta Lake.Config.Meta
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold, l_Array_append___redArg,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Name::{
    l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape,
    l_Lean_Name_toStringWithSep,
};
use crate::r#gen::Lake::Build::Facets::{
    initialize_Lake_Build_Facets, l_Lake_Module_oExportFacet, l_Lake_Module_oFacet,
    runtime_initialize_Lake_Build_Facets,
};
use crate::r#gen::Lake::Config::LeanConfig::{
    initialize_Lake_Config_LeanConfig, l_Lake_LeanConfig___fields,
    l_Lake_instInhabitedLeanConfig_default, runtime_initialize_Lake_Config_LeanConfig,
};
use crate::r#gen::Lake::Config::Meta::{
    initialize_Lake_Config_Meta, runtime_initialize_Lake_Config_Meta,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_usize_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
    lean_nat_dec_lt,
};
pub static l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [91, 97, 110, 111, 110, 121, 109, 111, 117, 115, 93, 0]};
static mut l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedLeanExeConfig_default___closed__0_value:
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
    m_fun: l_Lake_instInhabitedLeanExeConfig_default___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instInhabitedLeanExeConfig_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanExeConfig_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedLeanExeConfig_default___closed__1_value:
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
static mut l_Lake_instInhabitedLeanExeConfig_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanExeConfig_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedLeanExeConfig_default___closed__2_value:
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
    m_data: [45, 0],
};
static mut l_Lake_instInhabitedLeanExeConfig_default___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanExeConfig_default___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedLeanExeConfig_default___closed__3_value:
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
static mut l_Lake_instInhabitedLeanExeConfig_default___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanExeConfig_default___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_srcDir___proj___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanExeConfig_srcDir___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_srcDir___proj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_srcDir___proj___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanExeConfig_srcDir___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_srcDir___proj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_srcDir___proj___closed__2_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanExeConfig_srcDir___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_srcDir___proj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_srcDir___proj___closed__3_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanExeConfig_srcDir___proj___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_srcDir___proj___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_srcDir___proj___closed__4_value: crate::leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig_srcDir___proj___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_root___proj___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_root___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_root___proj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_root___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_root___proj___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_root___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_root___proj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_root___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_root___proj___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_root___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_root___proj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_root___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_exeName___proj___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanExeConfig_exeName___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_exeName___proj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_exeName___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_exeName___proj___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanExeConfig_exeName___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_exeName___proj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_exeName___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_exeName___proj___closed__2_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanExeConfig_exeName___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_exeName___proj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_exeName___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_needs___proj___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_needs___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_needs___proj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_needs___proj___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_needs___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_needs___proj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_needs___proj___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_needs___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_needs___proj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_needs___proj___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_needs___proj___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_needs___proj___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_needs___proj___closed__4_value: crate::leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig_needs___proj___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_extraDepTargets___proj___lam__3___closed__0_value:
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
static mut l_Lake_LeanExeConfig_extraDepTargets___proj___lam__3___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_extraDepTargets___proj___closed__0_value:
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
    m_fun: l_Lake_LeanExeConfig_extraDepTargets___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_extraDepTargets___proj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_extraDepTargets___proj___closed__1_value:
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
    m_fun: l_Lake_LeanExeConfig_extraDepTargets___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_extraDepTargets___proj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_extraDepTargets___proj___closed__2_value:
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
    m_fun: l_Lake_LeanExeConfig_extraDepTargets___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_extraDepTargets___proj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_extraDepTargets___proj___closed__3_value:
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
    m_fun: l_Lake_LeanExeConfig_extraDepTargets___proj___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_extraDepTargets___proj___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_extraDepTargets___proj___closed__4_value:
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
        core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig_extraDepTargets___proj___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_supportInterpreter___proj___closed__0_value:
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
    m_fun: l_Lake_LeanExeConfig_supportInterpreter___proj___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_supportInterpreter___proj___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_supportInterpreter___proj___closed__1_value:
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
    m_fun: l_Lake_LeanExeConfig_supportInterpreter___proj___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_supportInterpreter___proj___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_supportInterpreter___proj___closed__2_value:
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
    m_fun: l_Lake_LeanExeConfig_supportInterpreter___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_supportInterpreter___proj___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_supportInterpreter___proj___closed__3_value:
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
    m_fun: l_Lake_LeanExeConfig_supportInterpreter___proj___lam__3___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_supportInterpreter___proj___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_supportInterpreter___proj___closed__4_value:
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
        core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig_supportInterpreter___proj___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_nativeFacets___proj___closed__0_value:
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
    m_fun: l_Lake_LeanExeConfig_nativeFacets___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_nativeFacets___proj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_nativeFacets___proj___closed__1_value:
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
    m_fun: l_Lake_LeanExeConfig_nativeFacets___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_nativeFacets___proj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_nativeFacets___proj___closed__2_value:
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
    m_fun: l_Lake_LeanExeConfig_nativeFacets___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_nativeFacets___proj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_nativeFacets___proj___closed__3_value:
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
    m_fun: l_Lake_LeanExeConfig_nativeFacets___proj___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_nativeFacets___proj___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_nativeFacets___proj___closed__4_value:
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
        core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig_nativeFacets___proj___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value:
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
static mut l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__1_value:
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
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        515 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_toLeanConfig___proj___closed__0_value:
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
    m_fun: l_Lake_LeanExeConfig_toLeanConfig___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_toLeanConfig___proj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_toLeanConfig___proj___closed__1_value:
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
    m_fun: l_Lake_LeanExeConfig_toLeanConfig___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_toLeanConfig___proj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_toLeanConfig___proj___closed__2_value:
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
    m_fun: l_Lake_LeanExeConfig_toLeanConfig___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_toLeanConfig___proj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_toLeanConfig___proj___closed__3_value:
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
    m_fun: l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_toLeanConfig___proj___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_toLeanConfig___proj___closed__4_value:
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
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig_toLeanConfig___proj___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lake_LeanExeConfig___fields___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__1_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Lake_LeanExeConfig___fields___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__1_value)
                as *mut crate::leanh::LeanObject,
            10458569134091399506 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__2_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig___fields___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanExeConfig___fields___closed__5_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [114, 111, 111, 116, 0],
    };
static mut l_Lake_LeanExeConfig___fields___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__5_value)
                as *mut crate::leanh::LeanObject,
            13952697477363952342 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__6_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig___fields___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanExeConfig___fields___closed__9_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [101, 120, 101, 78, 97, 109, 101, 0],
    };
static mut l_Lake_LeanExeConfig___fields___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__9_value)
                as *mut crate::leanh::LeanObject,
            535955292391232655 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__10_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig___fields___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanExeConfig___fields___closed__13_value: crate::leanh::LeanStringObject<6> =
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
static mut l_Lake_LeanExeConfig___fields___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__14_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__13_value)
                as *mut crate::leanh::LeanObject,
            14359248566632897495 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__15_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__14_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__14_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig___fields___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanExeConfig___fields___closed__17_value: crate::leanh::LeanStringObject<16> =
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
static mut l_Lake_LeanExeConfig___fields___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__18_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__17_value)
                as *mut crate::leanh::LeanObject,
            376106234249747944 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__19_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__18_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__18_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__19_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig___fields___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanExeConfig___fields___closed__21_value: crate::leanh::LeanStringObject<19> =
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
            115, 117, 112, 112, 111, 114, 116, 73, 110, 116, 101, 114, 112, 114, 101, 116, 101,
            114, 0,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__22_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__21_value)
                as *mut crate::leanh::LeanObject,
            3358201691291746559 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__23_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__22_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__22_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__23_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig___fields___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanExeConfig___fields___closed__25_value: crate::leanh::LeanStringObject<13> =
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
static mut l_Lake_LeanExeConfig___fields___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__26_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__25_value)
                as *mut crate::leanh::LeanObject,
            2134236907718250370 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__27_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__26_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__26_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__27_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__28_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig___fields___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_LeanExeConfig___fields___closed__29_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig___fields___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanExeConfig___fields___closed__30_value: crate::leanh::LeanStringObject<13> =
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
static mut l_Lake_LeanExeConfig___fields___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__31_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__30_value)
                as *mut crate::leanh::LeanObject,
            782171420137495241 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__32_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__31_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__31_value)
                as *mut crate::leanh::LeanObject,
            256 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__32_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__33_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig___fields___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_LeanExeConfig___fields: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__1_value: crate::leanh::LeanClosureObject<
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
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__2_value: crate::leanh::LeanClosureObject<
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
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__3_value: crate::leanh::LeanClosureObject<
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
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__4_value: crate::leanh::LeanClosureObject<
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
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__5_value: crate::leanh::LeanClosureObject<
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
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__6_value: crate::leanh::LeanClosureObject<
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
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__7_value: crate::leanh::LeanClosureObject<
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
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__8_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__9_value: crate::leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__10_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__11: u8 = 0;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__12_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanExeConfig_instConfigInfo___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__13: u8 = 0;
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__14: usize = 0;
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_LeanExeConfig_instConfigInfo: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanExeConfig_instEmptyCollection___closed__0_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanExeConfig_instEmptyCollection___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lake_LeanExeConfig_instEmptyCollection___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instEmptyCollection___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_instInhabitedLeanExeConfig_default___lam__0(
    mut v_shouldExport_752_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_shouldExport_752_ == 0 {
                    v___x_758_ = l_Lake_Module_oFacet;
                    v___y_754_ = v___x_758_;
                    state = 1;
                    continue;
                } else {
                    v___x_759_ = l_Lake_Module_oExportFacet;
                    v___y_754_ = v___x_759_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_755_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_756_ = lean_mk_empty_array_with_capacity(v___x_755_);
                crate::leanh::lean_inc(v___y_754_);
                v___x_757_ = lean_array_push(v___x_756_, v___y_754_);
                return v___x_757_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instInhabitedLeanExeConfig_default___lam__0___boxed(
    mut v_shouldExport_760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_shouldExport_boxed_761_: u8 = 0;
    let mut v_res_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_shouldExport_boxed_761_ = (crate::leanh::lean_unbox(v_shouldExport_760_) as u8);
    v_res_762_ = l_Lake_instInhabitedLeanExeConfig_default___lam__0(v_shouldExport_boxed_761_);
    return v_res_762_;
}
pub unsafe fn l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0(
    mut v_sep_764_: *mut crate::leanh::LeanObject,
    mut v_escape_765_: u8,
    mut v_n_766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_n_766_) {
        0 => {
            let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_767_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0___closed__0;
            return v___x_767_;
        }
        1 => {
            let mut v_pre_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_pre_768_ = crate::leanh::lean_ctor_get(v_n_766_, 0);
            if crate::leanh::lean_obj_tag(v_pre_768_) == 0 {
                let mut v_str_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_770_: u8 = 0;
                let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_str_769_ = crate::leanh::lean_ctor_get(v_n_766_, 1);
                crate::leanh::lean_inc_ref(v_str_769_);
                crate::leanh::lean_dec_ref_known(v_n_766_, 2);
                v___x_770_ = 0;
                v___x_771_ =
                    l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(
                        v_escape_765_,
                        v_str_769_,
                        v___x_770_,
                    );
                return v___x_771_;
            } else {
                let mut v_str_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_r_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_775_: u8 = 0;
                let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_r_x27_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_inc(v_pre_768_);
                v_str_772_ = crate::leanh::lean_ctor_get(v_n_766_, 1);
                crate::leanh::lean_inc_ref(v_str_772_);
                crate::leanh::lean_dec_ref_known(v_n_766_, 2);
                v_r_773_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0(v_sep_764_, v_escape_765_, v_pre_768_);
                v___x_774_ = lean_string_append(v_r_773_, v_sep_764_);
                v___x_775_ = 0;
                v___x_776_ =
                    l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(
                        v_escape_765_,
                        v_str_772_,
                        v___x_775_,
                    );
                v_r_x27_777_ = lean_string_append(v___x_774_, v___x_776_);
                crate::leanh::lean_dec_ref(v___x_776_);
                return v_r_x27_777_;
            }
        }
        _ => {
            let mut v_pre_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_pre_778_ = crate::leanh::lean_ctor_get(v_n_766_, 0);
            if crate::leanh::lean_obj_tag(v_pre_778_) == 0 {
                let mut v_i_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_i_779_ = crate::leanh::lean_ctor_get(v_n_766_, 1);
                crate::leanh::lean_inc(v_i_779_);
                crate::leanh::lean_dec_ref_known(v_n_766_, 2);
                v___x_780_ = l_Nat_reprFast(v_i_779_);
                return v___x_780_;
            } else {
                let mut v_i_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_inc(v_pre_778_);
                v_i_781_ = crate::leanh::lean_ctor_get(v_n_766_, 1);
                crate::leanh::lean_inc(v_i_781_);
                crate::leanh::lean_dec_ref_known(v_n_766_, 2);
                v___x_782_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0(v_sep_764_, v_escape_765_, v_pre_778_);
                v___x_783_ = lean_string_append(v___x_782_, v_sep_764_);
                v___x_784_ = l_Nat_reprFast(v_i_781_);
                v___x_785_ = lean_string_append(v___x_783_, v___x_784_);
                crate::leanh::lean_dec_ref(v___x_784_);
                return v___x_785_;
            }
        }
    }
}
pub unsafe fn l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0___boxed(
    mut v_sep_786_: *mut crate::leanh::LeanObject,
    mut v_escape_787_: *mut crate::leanh::LeanObject,
    mut v_n_788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_escape_boxed_789_: u8 = 0;
    let mut v_res_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_escape_boxed_789_ = (crate::leanh::lean_unbox(v_escape_787_) as u8);
    v_res_790_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0(v_sep_786_, v_escape_boxed_789_, v_n_788_);
    crate::leanh::lean_dec_ref(v_sep_786_);
    return v_res_790_;
}
pub unsafe fn l_Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0(
    mut v_sep_791_: *mut crate::leanh::LeanObject,
    mut v_escape_792_: u8,
    mut v_n_793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_n_793_) {
        0 => {
            let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_794_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0___closed__0;
            return v___x_794_;
        }
        1 => {
            let mut v_pre_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_str_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_797_: u8 = 0;
            v_pre_795_ = crate::leanh::lean_ctor_get(v_n_793_, 0);
            crate::leanh::lean_inc(v_pre_795_);
            v_str_796_ = crate::leanh::lean_ctor_get(v_n_793_, 1);
            crate::leanh::lean_inc_ref(v_str_796_);
            crate::leanh::lean_dec_ref_known(v_n_793_, 2);
            v___x_797_ = 0;
            if crate::leanh::lean_obj_tag(v_pre_795_) == 0 {
                let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_798_ =
                    l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(
                        v_escape_792_,
                        v_str_796_,
                        v___x_797_,
                    );
                return v___x_798_;
            } else {
                let mut v_r_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_r_x27_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_r_799_ = l_Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0(v_sep_791_, v_escape_792_, v_pre_795_);
                v___x_800_ = lean_string_append(v_r_799_, v_sep_791_);
                v___x_801_ =
                    l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(
                        v_escape_792_,
                        v_str_796_,
                        v___x_797_,
                    );
                v_r_x27_802_ = lean_string_append(v___x_800_, v___x_801_);
                crate::leanh::lean_dec_ref(v___x_801_);
                return v_r_x27_802_;
            }
        }
        _ => {
            let mut v_pre_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_pre_803_ = crate::leanh::lean_ctor_get(v_n_793_, 0);
            if crate::leanh::lean_obj_tag(v_pre_803_) == 0 {
                let mut v_i_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_i_804_ = crate::leanh::lean_ctor_get(v_n_793_, 1);
                crate::leanh::lean_inc(v_i_804_);
                crate::leanh::lean_dec_ref_known(v_n_793_, 2);
                v___x_805_ = l_Nat_reprFast(v_i_804_);
                return v___x_805_;
            } else {
                let mut v_i_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_inc(v_pre_803_);
                v_i_806_ = crate::leanh::lean_ctor_get(v_n_793_, 1);
                crate::leanh::lean_inc(v_i_806_);
                crate::leanh::lean_dec_ref_known(v_n_793_, 2);
                v___x_807_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0(v_sep_791_, v_escape_792_, v_pre_803_);
                v___x_808_ = lean_string_append(v___x_807_, v_sep_791_);
                v___x_809_ = l_Nat_reprFast(v_i_806_);
                v___x_810_ = lean_string_append(v___x_808_, v___x_809_);
                crate::leanh::lean_dec_ref(v___x_809_);
                return v___x_810_;
            }
        }
    }
}
pub unsafe fn l_Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0___boxed(
    mut v_sep_811_: *mut crate::leanh::LeanObject,
    mut v_escape_812_: *mut crate::leanh::LeanObject,
    mut v_n_813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_escape_boxed_814_: u8 = 0;
    let mut v_res_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_escape_boxed_814_ = (crate::leanh::lean_unbox(v_escape_812_) as u8);
    v_res_815_ =
        l_Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0(
            v_sep_811_,
            v_escape_boxed_814_,
            v_n_813_,
        );
    crate::leanh::lean_dec_ref(v_sep_811_);
    return v_res_815_;
}
pub unsafe fn l_Lake_instInhabitedLeanExeConfig_default(
    mut v_name_821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: u8 = 0;
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_822_ = l_Lake_instInhabitedLeanExeConfig_default___closed__0;
    v___x_823_ = l_Lake_instInhabitedLeanConfig_default;
    v___x_824_ = l_Lake_instInhabitedLeanExeConfig_default___closed__1;
    v___x_825_ = l_Lake_instInhabitedLeanExeConfig_default___closed__2;
    v___x_826_ = 0;
    crate::leanh::lean_inc(v_name_821_);
    v___x_827_ =
        l_Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0(
            v___x_825_,
            v___x_826_,
            v_name_821_,
        );
    v___x_828_ = l_Lake_instInhabitedLeanExeConfig_default___closed__3;
    v___x_829_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_829_, 0, v___x_823_);
    crate::leanh::lean_ctor_set(v___x_829_, 1, v___x_824_);
    crate::leanh::lean_ctor_set(v___x_829_, 2, v_name_821_);
    crate::leanh::lean_ctor_set(v___x_829_, 3, v___x_827_);
    crate::leanh::lean_ctor_set(v___x_829_, 4, v___x_828_);
    crate::leanh::lean_ctor_set(v___x_829_, 5, v___x_828_);
    crate::leanh::lean_ctor_set(v___x_829_, 6, v___f_822_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_829_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
        v___x_826_,
    );
    return v___x_829_;
}
pub unsafe fn l_Lake_instInhabitedLeanExeConfig(
    mut v_a_830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_831_ = l_Lake_instInhabitedLeanExeConfig_default(v_a_830_);
    return v___x_831_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir___proj___lam__0(
    mut v_cfg_832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_srcDir_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_srcDir_833_ = crate::leanh::lean_ctor_get(v_cfg_832_, 1);
    crate::leanh::lean_inc_ref(v_srcDir_833_);
    return v_srcDir_833_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir___proj___lam__0___boxed(
    mut v_cfg_834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_835_ = l_Lake_LeanExeConfig_srcDir___proj___lam__0(v_cfg_834_);
    crate::leanh::lean_dec_ref(v_cfg_834_);
    return v_res_835_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir___proj___lam__1(
    mut v_val_836_: *mut crate::leanh::LeanObject,
    mut v_cfg_837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_843_: u8 = 0;
    let mut v_nativeFacets_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_847_: u8 = 0;
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_851_: u8 = 0;
    let mut v_unused_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_838_ = crate::leanh::lean_ctor_get(v_cfg_837_, 0);
                v_root_839_ = crate::leanh::lean_ctor_get(v_cfg_837_, 2);
                v_exeName_840_ = crate::leanh::lean_ctor_get(v_cfg_837_, 3);
                v_needs_841_ = crate::leanh::lean_ctor_get(v_cfg_837_, 4);
                v_extraDepTargets_842_ = crate::leanh::lean_ctor_get(v_cfg_837_, 5);
                v_supportInterpreter_843_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_837_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_844_ = crate::leanh::lean_ctor_get(v_cfg_837_, 6);
                v_isSharedCheck_851_ = (!crate::leanh::lean_is_exclusive(v_cfg_837_)) as u8;
                if v_isSharedCheck_851_ == 0 {
                    v_unused_852_ = crate::leanh::lean_ctor_get(v_cfg_837_, 1);
                    crate::leanh::lean_dec(v_unused_852_);
                    v___x_846_ = v_cfg_837_;
                    v_isShared_847_ = v_isSharedCheck_851_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_844_);
                    crate::leanh::lean_inc(v_extraDepTargets_842_);
                    crate::leanh::lean_inc(v_needs_841_);
                    crate::leanh::lean_inc(v_exeName_840_);
                    crate::leanh::lean_inc(v_root_839_);
                    crate::leanh::lean_inc(v_toLeanConfig_838_);
                    crate::leanh::lean_dec(v_cfg_837_);
                    v___x_846_ = crate::leanh::lean_box(0);
                    v_isShared_847_ = v_isSharedCheck_851_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_847_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_846_, 1, v_val_836_);
                    v___x_849_ = v___x_846_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_850_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_850_, 0, v_toLeanConfig_838_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_850_, 1, v_val_836_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_850_, 2, v_root_839_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_850_, 3, v_exeName_840_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_850_, 4, v_needs_841_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_850_, 5, v_extraDepTargets_842_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_850_, 6, v_nativeFacets_844_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_850_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_supportInterpreter_843_,
                    );
                    v___x_849_ = v_reuseFailAlloc_850_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_849_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir___proj___lam__2(
    mut v_f_853_: *mut crate::leanh::LeanObject,
    mut v_cfg_854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_861_: u8 = 0;
    let mut v_nativeFacets_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_865_: u8 = 0;
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_870_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_855_ = crate::leanh::lean_ctor_get(v_cfg_854_, 0);
                v_srcDir_856_ = crate::leanh::lean_ctor_get(v_cfg_854_, 1);
                v_root_857_ = crate::leanh::lean_ctor_get(v_cfg_854_, 2);
                v_exeName_858_ = crate::leanh::lean_ctor_get(v_cfg_854_, 3);
                v_needs_859_ = crate::leanh::lean_ctor_get(v_cfg_854_, 4);
                v_extraDepTargets_860_ = crate::leanh::lean_ctor_get(v_cfg_854_, 5);
                v_supportInterpreter_861_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_854_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_862_ = crate::leanh::lean_ctor_get(v_cfg_854_, 6);
                v_isSharedCheck_870_ = (!crate::leanh::lean_is_exclusive(v_cfg_854_)) as u8;
                if v_isSharedCheck_870_ == 0 {
                    v___x_864_ = v_cfg_854_;
                    v_isShared_865_ = v_isSharedCheck_870_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_862_);
                    crate::leanh::lean_inc(v_extraDepTargets_860_);
                    crate::leanh::lean_inc(v_needs_859_);
                    crate::leanh::lean_inc(v_exeName_858_);
                    crate::leanh::lean_inc(v_root_857_);
                    crate::leanh::lean_inc(v_srcDir_856_);
                    crate::leanh::lean_inc(v_toLeanConfig_855_);
                    crate::leanh::lean_dec(v_cfg_854_);
                    v___x_864_ = crate::leanh::lean_box(0);
                    v_isShared_865_ = v_isSharedCheck_870_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_866_ = crate::leanh::lean_apply_1(v_f_853_, v_srcDir_856_);
                if v_isShared_865_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_864_, 1, v___x_866_);
                    v___x_868_ = v___x_864_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_869_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_869_, 0, v_toLeanConfig_855_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_869_, 2, v_root_857_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_869_, 3, v_exeName_858_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_869_, 4, v_needs_859_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_869_, 5, v_extraDepTargets_860_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_869_, 6, v_nativeFacets_862_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_869_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_supportInterpreter_861_,
                    );
                    v___x_868_ = v_reuseFailAlloc_869_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_868_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir___proj___lam__3(
    mut v_x_871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_872_ = l_Lake_instInhabitedLeanExeConfig_default___closed__1;
    return v___x_872_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir___proj___lam__3___boxed(
    mut v_x_873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_874_ = l_Lake_LeanExeConfig_srcDir___proj___lam__3(v_x_873_);
    crate::leanh::lean_dec_ref(v_x_873_);
    return v_res_874_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir___proj(
    mut v_name_884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_885_ = l_Lake_LeanExeConfig_srcDir___proj___closed__4;
    return v___x_885_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir___proj___boxed(
    mut v_name_886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_887_ = l_Lake_LeanExeConfig_srcDir___proj(v_name_886_);
    crate::leanh::lean_dec(v_name_886_);
    return v_res_887_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir_instConfigField(
    mut v_name_888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_889_ = l_Lake_LeanExeConfig_srcDir___proj(v_name_888_);
    return v___x_889_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir_instConfigField___boxed(
    mut v_name_890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_891_ = l_Lake_LeanExeConfig_srcDir_instConfigField(v_name_890_);
    crate::leanh::lean_dec(v_name_890_);
    return v_res_891_;
}
pub unsafe fn l_Lake_LeanExeConfig_root___proj___lam__0(
    mut v_cfg_892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_root_893_ = crate::leanh::lean_ctor_get(v_cfg_892_, 2);
    crate::leanh::lean_inc(v_root_893_);
    return v_root_893_;
}
pub unsafe fn l_Lake_LeanExeConfig_root___proj___lam__0___boxed(
    mut v_cfg_894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_895_ = l_Lake_LeanExeConfig_root___proj___lam__0(v_cfg_894_);
    crate::leanh::lean_dec_ref(v_cfg_894_);
    return v_res_895_;
}
pub unsafe fn l_Lake_LeanExeConfig_root___proj___lam__1(
    mut v_val_896_: *mut crate::leanh::LeanObject,
    mut v_cfg_897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_903_: u8 = 0;
    let mut v_nativeFacets_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_907_: u8 = 0;
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_911_: u8 = 0;
    let mut v_unused_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_898_ = crate::leanh::lean_ctor_get(v_cfg_897_, 0);
                v_srcDir_899_ = crate::leanh::lean_ctor_get(v_cfg_897_, 1);
                v_exeName_900_ = crate::leanh::lean_ctor_get(v_cfg_897_, 3);
                v_needs_901_ = crate::leanh::lean_ctor_get(v_cfg_897_, 4);
                v_extraDepTargets_902_ = crate::leanh::lean_ctor_get(v_cfg_897_, 5);
                v_supportInterpreter_903_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_897_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_904_ = crate::leanh::lean_ctor_get(v_cfg_897_, 6);
                v_isSharedCheck_911_ = (!crate::leanh::lean_is_exclusive(v_cfg_897_)) as u8;
                if v_isSharedCheck_911_ == 0 {
                    v_unused_912_ = crate::leanh::lean_ctor_get(v_cfg_897_, 2);
                    crate::leanh::lean_dec(v_unused_912_);
                    v___x_906_ = v_cfg_897_;
                    v_isShared_907_ = v_isSharedCheck_911_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_904_);
                    crate::leanh::lean_inc(v_extraDepTargets_902_);
                    crate::leanh::lean_inc(v_needs_901_);
                    crate::leanh::lean_inc(v_exeName_900_);
                    crate::leanh::lean_inc(v_srcDir_899_);
                    crate::leanh::lean_inc(v_toLeanConfig_898_);
                    crate::leanh::lean_dec(v_cfg_897_);
                    v___x_906_ = crate::leanh::lean_box(0);
                    v_isShared_907_ = v_isSharedCheck_911_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_907_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_906_, 2, v_val_896_);
                    v___x_909_ = v___x_906_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_910_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_910_, 0, v_toLeanConfig_898_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_910_, 1, v_srcDir_899_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_910_, 2, v_val_896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_910_, 3, v_exeName_900_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_910_, 4, v_needs_901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_910_, 5, v_extraDepTargets_902_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_910_, 6, v_nativeFacets_904_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_910_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_supportInterpreter_903_,
                    );
                    v___x_909_ = v_reuseFailAlloc_910_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_909_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_root___proj___lam__2(
    mut v_f_913_: *mut crate::leanh::LeanObject,
    mut v_cfg_914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_921_: u8 = 0;
    let mut v_nativeFacets_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_925_: u8 = 0;
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_915_ = crate::leanh::lean_ctor_get(v_cfg_914_, 0);
                v_srcDir_916_ = crate::leanh::lean_ctor_get(v_cfg_914_, 1);
                v_root_917_ = crate::leanh::lean_ctor_get(v_cfg_914_, 2);
                v_exeName_918_ = crate::leanh::lean_ctor_get(v_cfg_914_, 3);
                v_needs_919_ = crate::leanh::lean_ctor_get(v_cfg_914_, 4);
                v_extraDepTargets_920_ = crate::leanh::lean_ctor_get(v_cfg_914_, 5);
                v_supportInterpreter_921_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_914_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_922_ = crate::leanh::lean_ctor_get(v_cfg_914_, 6);
                v_isSharedCheck_930_ = (!crate::leanh::lean_is_exclusive(v_cfg_914_)) as u8;
                if v_isSharedCheck_930_ == 0 {
                    v___x_924_ = v_cfg_914_;
                    v_isShared_925_ = v_isSharedCheck_930_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_922_);
                    crate::leanh::lean_inc(v_extraDepTargets_920_);
                    crate::leanh::lean_inc(v_needs_919_);
                    crate::leanh::lean_inc(v_exeName_918_);
                    crate::leanh::lean_inc(v_root_917_);
                    crate::leanh::lean_inc(v_srcDir_916_);
                    crate::leanh::lean_inc(v_toLeanConfig_915_);
                    crate::leanh::lean_dec(v_cfg_914_);
                    v___x_924_ = crate::leanh::lean_box(0);
                    v_isShared_925_ = v_isSharedCheck_930_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_926_ = crate::leanh::lean_apply_1(v_f_913_, v_root_917_);
                if v_isShared_925_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_924_, 2, v___x_926_);
                    v___x_928_ = v___x_924_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_929_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_929_, 0, v_toLeanConfig_915_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_929_, 1, v_srcDir_916_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_929_, 2, v___x_926_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_929_, 3, v_exeName_918_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_929_, 4, v_needs_919_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_929_, 5, v_extraDepTargets_920_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_929_, 6, v_nativeFacets_922_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_929_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_supportInterpreter_921_,
                    );
                    v___x_928_ = v_reuseFailAlloc_929_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_928_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_root___proj___lam__3(
    mut v_name_931_: *mut crate::leanh::LeanObject,
    mut v_x_932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_name_931_);
    return v_name_931_;
}
pub unsafe fn l_Lake_LeanExeConfig_root___proj___lam__3___boxed(
    mut v_name_933_: *mut crate::leanh::LeanObject,
    mut v_x_934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_935_ = l_Lake_LeanExeConfig_root___proj___lam__3(v_name_933_, v_x_934_);
    crate::leanh::lean_dec_ref(v_x_934_);
    crate::leanh::lean_dec(v_name_933_);
    return v_res_935_;
}
pub unsafe fn l_Lake_LeanExeConfig_root___proj(
    mut v_name_939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_940_ = l_Lake_LeanExeConfig_root___proj___closed__0;
    v___f_941_ = l_Lake_LeanExeConfig_root___proj___closed__1;
    v___f_942_ = l_Lake_LeanExeConfig_root___proj___closed__2;
    v___f_943_ = crate::leanh::lean_alloc_closure(
        l_Lake_LeanExeConfig_root___proj___lam__3___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_943_, 0, v_name_939_);
    v___x_944_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_944_, 0, v___f_940_);
    crate::leanh::lean_ctor_set(v___x_944_, 1, v___f_941_);
    crate::leanh::lean_ctor_set(v___x_944_, 2, v___f_942_);
    crate::leanh::lean_ctor_set(v___x_944_, 3, v___f_943_);
    return v___x_944_;
}
pub unsafe fn l_Lake_LeanExeConfig_root_instConfigField(
    mut v_name_945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_946_ = l_Lake_LeanExeConfig_root___proj(v_name_945_);
    return v___x_946_;
}
pub unsafe fn l_Lake_LeanExeConfig_exeName___proj___lam__0(
    mut v_cfg_947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_exeName_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_exeName_948_ = crate::leanh::lean_ctor_get(v_cfg_947_, 3);
    crate::leanh::lean_inc_ref(v_exeName_948_);
    return v_exeName_948_;
}
pub unsafe fn l_Lake_LeanExeConfig_exeName___proj___lam__0___boxed(
    mut v_cfg_949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_950_ = l_Lake_LeanExeConfig_exeName___proj___lam__0(v_cfg_949_);
    crate::leanh::lean_dec_ref(v_cfg_949_);
    return v_res_950_;
}
pub unsafe fn l_Lake_LeanExeConfig_exeName___proj___lam__1(
    mut v_val_951_: *mut crate::leanh::LeanObject,
    mut v_cfg_952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_958_: u8 = 0;
    let mut v_nativeFacets_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_962_: u8 = 0;
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_966_: u8 = 0;
    let mut v_unused_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_953_ = crate::leanh::lean_ctor_get(v_cfg_952_, 0);
                v_srcDir_954_ = crate::leanh::lean_ctor_get(v_cfg_952_, 1);
                v_root_955_ = crate::leanh::lean_ctor_get(v_cfg_952_, 2);
                v_needs_956_ = crate::leanh::lean_ctor_get(v_cfg_952_, 4);
                v_extraDepTargets_957_ = crate::leanh::lean_ctor_get(v_cfg_952_, 5);
                v_supportInterpreter_958_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_952_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_959_ = crate::leanh::lean_ctor_get(v_cfg_952_, 6);
                v_isSharedCheck_966_ = (!crate::leanh::lean_is_exclusive(v_cfg_952_)) as u8;
                if v_isSharedCheck_966_ == 0 {
                    v_unused_967_ = crate::leanh::lean_ctor_get(v_cfg_952_, 3);
                    crate::leanh::lean_dec(v_unused_967_);
                    v___x_961_ = v_cfg_952_;
                    v_isShared_962_ = v_isSharedCheck_966_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_959_);
                    crate::leanh::lean_inc(v_extraDepTargets_957_);
                    crate::leanh::lean_inc(v_needs_956_);
                    crate::leanh::lean_inc(v_root_955_);
                    crate::leanh::lean_inc(v_srcDir_954_);
                    crate::leanh::lean_inc(v_toLeanConfig_953_);
                    crate::leanh::lean_dec(v_cfg_952_);
                    v___x_961_ = crate::leanh::lean_box(0);
                    v_isShared_962_ = v_isSharedCheck_966_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_962_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_961_, 3, v_val_951_);
                    v___x_964_ = v___x_961_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_965_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_965_, 0, v_toLeanConfig_953_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_965_, 1, v_srcDir_954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_965_, 2, v_root_955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_965_, 3, v_val_951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_965_, 4, v_needs_956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_965_, 5, v_extraDepTargets_957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_965_, 6, v_nativeFacets_959_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_965_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_supportInterpreter_958_,
                    );
                    v___x_964_ = v_reuseFailAlloc_965_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_964_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_exeName___proj___lam__2(
    mut v_f_968_: *mut crate::leanh::LeanObject,
    mut v_cfg_969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_976_: u8 = 0;
    let mut v_nativeFacets_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_980_: u8 = 0;
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_985_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_970_ = crate::leanh::lean_ctor_get(v_cfg_969_, 0);
                v_srcDir_971_ = crate::leanh::lean_ctor_get(v_cfg_969_, 1);
                v_root_972_ = crate::leanh::lean_ctor_get(v_cfg_969_, 2);
                v_exeName_973_ = crate::leanh::lean_ctor_get(v_cfg_969_, 3);
                v_needs_974_ = crate::leanh::lean_ctor_get(v_cfg_969_, 4);
                v_extraDepTargets_975_ = crate::leanh::lean_ctor_get(v_cfg_969_, 5);
                v_supportInterpreter_976_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_969_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_977_ = crate::leanh::lean_ctor_get(v_cfg_969_, 6);
                v_isSharedCheck_985_ = (!crate::leanh::lean_is_exclusive(v_cfg_969_)) as u8;
                if v_isSharedCheck_985_ == 0 {
                    v___x_979_ = v_cfg_969_;
                    v_isShared_980_ = v_isSharedCheck_985_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_977_);
                    crate::leanh::lean_inc(v_extraDepTargets_975_);
                    crate::leanh::lean_inc(v_needs_974_);
                    crate::leanh::lean_inc(v_exeName_973_);
                    crate::leanh::lean_inc(v_root_972_);
                    crate::leanh::lean_inc(v_srcDir_971_);
                    crate::leanh::lean_inc(v_toLeanConfig_970_);
                    crate::leanh::lean_dec(v_cfg_969_);
                    v___x_979_ = crate::leanh::lean_box(0);
                    v_isShared_980_ = v_isSharedCheck_985_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_981_ = crate::leanh::lean_apply_1(v_f_968_, v_exeName_973_);
                if v_isShared_980_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_979_, 3, v___x_981_);
                    v___x_983_ = v___x_979_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_984_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_984_, 0, v_toLeanConfig_970_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_984_, 1, v_srcDir_971_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_984_, 2, v_root_972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_984_, 3, v___x_981_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_984_, 4, v_needs_974_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_984_, 5, v_extraDepTargets_975_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_984_, 6, v_nativeFacets_977_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_984_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_supportInterpreter_976_,
                    );
                    v___x_983_ = v_reuseFailAlloc_984_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_983_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_exeName___proj___lam__3(
    mut v_name_986_: *mut crate::leanh::LeanObject,
    mut v_x_987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: u8 = 0;
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_988_ = l_Lake_instInhabitedLeanExeConfig_default___closed__2;
    v___x_989_ = 0;
    v___x_990_ =
        l_Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0(
            v___x_988_,
            v___x_989_,
            v_name_986_,
        );
    return v___x_990_;
}
pub unsafe fn l_Lake_LeanExeConfig_exeName___proj___lam__3___boxed(
    mut v_name_991_: *mut crate::leanh::LeanObject,
    mut v_x_992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_993_ = l_Lake_LeanExeConfig_exeName___proj___lam__3(v_name_991_, v_x_992_);
    crate::leanh::lean_dec_ref(v_x_992_);
    return v_res_993_;
}
pub unsafe fn l_Lake_LeanExeConfig_exeName___proj(
    mut v_name_997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_998_ = l_Lake_LeanExeConfig_exeName___proj___closed__0;
    v___f_999_ = l_Lake_LeanExeConfig_exeName___proj___closed__1;
    v___f_1000_ = l_Lake_LeanExeConfig_exeName___proj___closed__2;
    v___f_1001_ = crate::leanh::lean_alloc_closure(
        l_Lake_LeanExeConfig_exeName___proj___lam__3___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1001_, 0, v_name_997_);
    v___x_1002_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1002_, 0, v___f_998_);
    crate::leanh::lean_ctor_set(v___x_1002_, 1, v___f_999_);
    crate::leanh::lean_ctor_set(v___x_1002_, 2, v___f_1000_);
    crate::leanh::lean_ctor_set(v___x_1002_, 3, v___f_1001_);
    return v___x_1002_;
}
pub unsafe fn l_Lake_LeanExeConfig_exeName_instConfigField(
    mut v_name_1003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1004_ = l_Lake_LeanExeConfig_exeName___proj(v_name_1003_);
    return v___x_1004_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs___proj___lam__0(
    mut v_cfg_1005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_needs_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_needs_1006_ = crate::leanh::lean_ctor_get(v_cfg_1005_, 4);
    crate::leanh::lean_inc_ref(v_needs_1006_);
    return v_needs_1006_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs___proj___lam__0___boxed(
    mut v_cfg_1007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1008_ = l_Lake_LeanExeConfig_needs___proj___lam__0(v_cfg_1007_);
    crate::leanh::lean_dec_ref(v_cfg_1007_);
    return v_res_1008_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs___proj___lam__1(
    mut v_val_1009_: *mut crate::leanh::LeanObject,
    mut v_cfg_1010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1016_: u8 = 0;
    let mut v_nativeFacets_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1020_: u8 = 0;
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1024_: u8 = 0;
    let mut v_unused_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1011_ = crate::leanh::lean_ctor_get(v_cfg_1010_, 0);
                v_srcDir_1012_ = crate::leanh::lean_ctor_get(v_cfg_1010_, 1);
                v_root_1013_ = crate::leanh::lean_ctor_get(v_cfg_1010_, 2);
                v_exeName_1014_ = crate::leanh::lean_ctor_get(v_cfg_1010_, 3);
                v_extraDepTargets_1015_ = crate::leanh::lean_ctor_get(v_cfg_1010_, 5);
                v_supportInterpreter_1016_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1010_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1017_ = crate::leanh::lean_ctor_get(v_cfg_1010_, 6);
                v_isSharedCheck_1024_ = (!crate::leanh::lean_is_exclusive(v_cfg_1010_)) as u8;
                if v_isSharedCheck_1024_ == 0 {
                    v_unused_1025_ = crate::leanh::lean_ctor_get(v_cfg_1010_, 4);
                    crate::leanh::lean_dec(v_unused_1025_);
                    v___x_1019_ = v_cfg_1010_;
                    v_isShared_1020_ = v_isSharedCheck_1024_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1017_);
                    crate::leanh::lean_inc(v_extraDepTargets_1015_);
                    crate::leanh::lean_inc(v_exeName_1014_);
                    crate::leanh::lean_inc(v_root_1013_);
                    crate::leanh::lean_inc(v_srcDir_1012_);
                    crate::leanh::lean_inc(v_toLeanConfig_1011_);
                    crate::leanh::lean_dec(v_cfg_1010_);
                    v___x_1019_ = crate::leanh::lean_box(0);
                    v_isShared_1020_ = v_isSharedCheck_1024_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1020_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1019_, 4, v_val_1009_);
                    v___x_1022_ = v___x_1019_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1023_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_toLeanConfig_1011_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_srcDir_1012_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1023_, 2, v_root_1013_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1023_, 3, v_exeName_1014_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1023_, 4, v_val_1009_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1023_, 5, v_extraDepTargets_1015_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1023_, 6, v_nativeFacets_1017_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1023_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_supportInterpreter_1016_,
                    );
                    v___x_1022_ = v_reuseFailAlloc_1023_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1022_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_needs___proj___lam__2(
    mut v_f_1026_: *mut crate::leanh::LeanObject,
    mut v_cfg_1027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1034_: u8 = 0;
    let mut v_nativeFacets_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1038_: u8 = 0;
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1028_ = crate::leanh::lean_ctor_get(v_cfg_1027_, 0);
                v_srcDir_1029_ = crate::leanh::lean_ctor_get(v_cfg_1027_, 1);
                v_root_1030_ = crate::leanh::lean_ctor_get(v_cfg_1027_, 2);
                v_exeName_1031_ = crate::leanh::lean_ctor_get(v_cfg_1027_, 3);
                v_needs_1032_ = crate::leanh::lean_ctor_get(v_cfg_1027_, 4);
                v_extraDepTargets_1033_ = crate::leanh::lean_ctor_get(v_cfg_1027_, 5);
                v_supportInterpreter_1034_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1027_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1035_ = crate::leanh::lean_ctor_get(v_cfg_1027_, 6);
                v_isSharedCheck_1043_ = (!crate::leanh::lean_is_exclusive(v_cfg_1027_)) as u8;
                if v_isSharedCheck_1043_ == 0 {
                    v___x_1037_ = v_cfg_1027_;
                    v_isShared_1038_ = v_isSharedCheck_1043_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1035_);
                    crate::leanh::lean_inc(v_extraDepTargets_1033_);
                    crate::leanh::lean_inc(v_needs_1032_);
                    crate::leanh::lean_inc(v_exeName_1031_);
                    crate::leanh::lean_inc(v_root_1030_);
                    crate::leanh::lean_inc(v_srcDir_1029_);
                    crate::leanh::lean_inc(v_toLeanConfig_1028_);
                    crate::leanh::lean_dec(v_cfg_1027_);
                    v___x_1037_ = crate::leanh::lean_box(0);
                    v_isShared_1038_ = v_isSharedCheck_1043_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1039_ = crate::leanh::lean_apply_1(v_f_1026_, v_needs_1032_);
                if v_isShared_1038_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1037_, 4, v___x_1039_);
                    v___x_1041_ = v___x_1037_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1042_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_toLeanConfig_1028_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_srcDir_1029_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 2, v_root_1030_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 3, v_exeName_1031_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 4, v___x_1039_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 5, v_extraDepTargets_1033_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 6, v_nativeFacets_1035_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1042_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_supportInterpreter_1034_,
                    );
                    v___x_1041_ = v_reuseFailAlloc_1042_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1041_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_needs___proj___lam__3(
    mut v_x_1044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1045_ = l_Lake_instInhabitedLeanExeConfig_default___closed__3;
    return v___x_1045_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs___proj___lam__3___boxed(
    mut v_x_1046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1047_ = l_Lake_LeanExeConfig_needs___proj___lam__3(v_x_1046_);
    crate::leanh::lean_dec_ref(v_x_1046_);
    return v_res_1047_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs___proj(
    mut v_name_1057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1058_ = l_Lake_LeanExeConfig_needs___proj___closed__4;
    return v___x_1058_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs___proj___boxed(
    mut v_name_1059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1060_ = l_Lake_LeanExeConfig_needs___proj(v_name_1059_);
    crate::leanh::lean_dec(v_name_1059_);
    return v_res_1060_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs_instConfigField(
    mut v_name_1061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1062_ = l_Lake_LeanExeConfig_needs___proj(v_name_1061_);
    return v___x_1062_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs_instConfigField___boxed(
    mut v_name_1063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1064_ = l_Lake_LeanExeConfig_needs_instConfigField(v_name_1063_);
    crate::leanh::lean_dec(v_name_1063_);
    return v_res_1064_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets___proj___lam__0(
    mut v_cfg_1065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_extraDepTargets_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_extraDepTargets_1066_ = crate::leanh::lean_ctor_get(v_cfg_1065_, 5);
    crate::leanh::lean_inc_ref(v_extraDepTargets_1066_);
    return v_extraDepTargets_1066_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets___proj___lam__0___boxed(
    mut v_cfg_1067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1068_ = l_Lake_LeanExeConfig_extraDepTargets___proj___lam__0(v_cfg_1067_);
    crate::leanh::lean_dec_ref(v_cfg_1067_);
    return v_res_1068_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets___proj___lam__1(
    mut v_val_1069_: *mut crate::leanh::LeanObject,
    mut v_cfg_1070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1076_: u8 = 0;
    let mut v_nativeFacets_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1080_: u8 = 0;
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1084_: u8 = 0;
    let mut v_unused_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1071_ = crate::leanh::lean_ctor_get(v_cfg_1070_, 0);
                v_srcDir_1072_ = crate::leanh::lean_ctor_get(v_cfg_1070_, 1);
                v_root_1073_ = crate::leanh::lean_ctor_get(v_cfg_1070_, 2);
                v_exeName_1074_ = crate::leanh::lean_ctor_get(v_cfg_1070_, 3);
                v_needs_1075_ = crate::leanh::lean_ctor_get(v_cfg_1070_, 4);
                v_supportInterpreter_1076_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1070_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1077_ = crate::leanh::lean_ctor_get(v_cfg_1070_, 6);
                v_isSharedCheck_1084_ = (!crate::leanh::lean_is_exclusive(v_cfg_1070_)) as u8;
                if v_isSharedCheck_1084_ == 0 {
                    v_unused_1085_ = crate::leanh::lean_ctor_get(v_cfg_1070_, 5);
                    crate::leanh::lean_dec(v_unused_1085_);
                    v___x_1079_ = v_cfg_1070_;
                    v_isShared_1080_ = v_isSharedCheck_1084_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1077_);
                    crate::leanh::lean_inc(v_needs_1075_);
                    crate::leanh::lean_inc(v_exeName_1074_);
                    crate::leanh::lean_inc(v_root_1073_);
                    crate::leanh::lean_inc(v_srcDir_1072_);
                    crate::leanh::lean_inc(v_toLeanConfig_1071_);
                    crate::leanh::lean_dec(v_cfg_1070_);
                    v___x_1079_ = crate::leanh::lean_box(0);
                    v_isShared_1080_ = v_isSharedCheck_1084_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1080_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1079_, 5, v_val_1069_);
                    v___x_1082_ = v___x_1079_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1083_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_toLeanConfig_1071_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_srcDir_1072_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 2, v_root_1073_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 3, v_exeName_1074_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 4, v_needs_1075_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 5, v_val_1069_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 6, v_nativeFacets_1077_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1083_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_supportInterpreter_1076_,
                    );
                    v___x_1082_ = v_reuseFailAlloc_1083_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1082_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets___proj___lam__2(
    mut v_f_1086_: *mut crate::leanh::LeanObject,
    mut v_cfg_1087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1094_: u8 = 0;
    let mut v_nativeFacets_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1098_: u8 = 0;
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1103_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1088_ = crate::leanh::lean_ctor_get(v_cfg_1087_, 0);
                v_srcDir_1089_ = crate::leanh::lean_ctor_get(v_cfg_1087_, 1);
                v_root_1090_ = crate::leanh::lean_ctor_get(v_cfg_1087_, 2);
                v_exeName_1091_ = crate::leanh::lean_ctor_get(v_cfg_1087_, 3);
                v_needs_1092_ = crate::leanh::lean_ctor_get(v_cfg_1087_, 4);
                v_extraDepTargets_1093_ = crate::leanh::lean_ctor_get(v_cfg_1087_, 5);
                v_supportInterpreter_1094_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1087_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1095_ = crate::leanh::lean_ctor_get(v_cfg_1087_, 6);
                v_isSharedCheck_1103_ = (!crate::leanh::lean_is_exclusive(v_cfg_1087_)) as u8;
                if v_isSharedCheck_1103_ == 0 {
                    v___x_1097_ = v_cfg_1087_;
                    v_isShared_1098_ = v_isSharedCheck_1103_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1095_);
                    crate::leanh::lean_inc(v_extraDepTargets_1093_);
                    crate::leanh::lean_inc(v_needs_1092_);
                    crate::leanh::lean_inc(v_exeName_1091_);
                    crate::leanh::lean_inc(v_root_1090_);
                    crate::leanh::lean_inc(v_srcDir_1089_);
                    crate::leanh::lean_inc(v_toLeanConfig_1088_);
                    crate::leanh::lean_dec(v_cfg_1087_);
                    v___x_1097_ = crate::leanh::lean_box(0);
                    v_isShared_1098_ = v_isSharedCheck_1103_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1099_ = crate::leanh::lean_apply_1(v_f_1086_, v_extraDepTargets_1093_);
                if v_isShared_1098_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1097_, 5, v___x_1099_);
                    v___x_1101_ = v___x_1097_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1102_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_toLeanConfig_1088_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_srcDir_1089_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1102_, 2, v_root_1090_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1102_, 3, v_exeName_1091_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1102_, 4, v_needs_1092_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1102_, 5, v___x_1099_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1102_, 6, v_nativeFacets_1095_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1102_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_supportInterpreter_1094_,
                    );
                    v___x_1101_ = v_reuseFailAlloc_1102_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1101_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets___proj___lam__3(
    mut v_x_1106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1107_ = l_Lake_LeanExeConfig_extraDepTargets___proj___lam__3___closed__0;
    return v___x_1107_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets___proj___lam__3___boxed(
    mut v_x_1108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1109_ = l_Lake_LeanExeConfig_extraDepTargets___proj___lam__3(v_x_1108_);
    crate::leanh::lean_dec_ref(v_x_1108_);
    return v_res_1109_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets___proj(
    mut v_name_1119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1120_ = l_Lake_LeanExeConfig_extraDepTargets___proj___closed__4;
    return v___x_1120_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets___proj___boxed(
    mut v_name_1121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1122_ = l_Lake_LeanExeConfig_extraDepTargets___proj(v_name_1121_);
    crate::leanh::lean_dec(v_name_1121_);
    return v_res_1122_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets_instConfigField(
    mut v_name_1123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1124_ = l_Lake_LeanExeConfig_extraDepTargets___proj(v_name_1123_);
    return v___x_1124_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets_instConfigField___boxed(
    mut v_name_1125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1126_ = l_Lake_LeanExeConfig_extraDepTargets_instConfigField(v_name_1125_);
    crate::leanh::lean_dec(v_name_1125_);
    return v_res_1126_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___lam__0(
    mut v_cfg_1127_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_supportInterpreter_1128_: u8 = 0;
    v_supportInterpreter_1128_ = crate::leanh::lean_ctor_get_uint8(
        v_cfg_1127_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
    );
    return v_supportInterpreter_1128_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___lam__0___boxed(
    mut v_cfg_1129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1130_: u8 = 0;
    let mut v_r_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1130_ = l_Lake_LeanExeConfig_supportInterpreter___proj___lam__0(v_cfg_1129_);
    crate::leanh::lean_dec_ref(v_cfg_1129_);
    v_r_1131_ = crate::leanh::lean_box((v_res_1130_) as usize);
    return v_r_1131_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___lam__1(
    mut v_val_1132_: u8,
    mut v_cfg_1133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1143_: u8 = 0;
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1147_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1134_ = crate::leanh::lean_ctor_get(v_cfg_1133_, 0);
                v_srcDir_1135_ = crate::leanh::lean_ctor_get(v_cfg_1133_, 1);
                v_root_1136_ = crate::leanh::lean_ctor_get(v_cfg_1133_, 2);
                v_exeName_1137_ = crate::leanh::lean_ctor_get(v_cfg_1133_, 3);
                v_needs_1138_ = crate::leanh::lean_ctor_get(v_cfg_1133_, 4);
                v_extraDepTargets_1139_ = crate::leanh::lean_ctor_get(v_cfg_1133_, 5);
                v_nativeFacets_1140_ = crate::leanh::lean_ctor_get(v_cfg_1133_, 6);
                v_isSharedCheck_1147_ = (!crate::leanh::lean_is_exclusive(v_cfg_1133_)) as u8;
                if v_isSharedCheck_1147_ == 0 {
                    v___x_1142_ = v_cfg_1133_;
                    v_isShared_1143_ = v_isSharedCheck_1147_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1140_);
                    crate::leanh::lean_inc(v_extraDepTargets_1139_);
                    crate::leanh::lean_inc(v_needs_1138_);
                    crate::leanh::lean_inc(v_exeName_1137_);
                    crate::leanh::lean_inc(v_root_1136_);
                    crate::leanh::lean_inc(v_srcDir_1135_);
                    crate::leanh::lean_inc(v_toLeanConfig_1134_);
                    crate::leanh::lean_dec(v_cfg_1133_);
                    v___x_1142_ = crate::leanh::lean_box(0);
                    v_isShared_1143_ = v_isSharedCheck_1147_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1143_ == 0 {
                    v___x_1145_ = v___x_1142_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1146_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_toLeanConfig_1134_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_srcDir_1135_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 2, v_root_1136_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 3, v_exeName_1137_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 4, v_needs_1138_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 5, v_extraDepTargets_1139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 6, v_nativeFacets_1140_);
                    v___x_1145_ = v_reuseFailAlloc_1146_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1145_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_val_1132_,
                );
                return v___x_1145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___lam__1___boxed(
    mut v_val_1148_: *mut crate::leanh::LeanObject,
    mut v_cfg_1149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_59__boxed_1150_: u8 = 0;
    let mut v_res_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_59__boxed_1150_ = (crate::leanh::lean_unbox(v_val_1148_) as u8);
    v_res_1151_ =
        l_Lake_LeanExeConfig_supportInterpreter___proj___lam__1(v_val_59__boxed_1150_, v_cfg_1149_);
    return v_res_1151_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___lam__2(
    mut v_f_1152_: *mut crate::leanh::LeanObject,
    mut v_cfg_1153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1160_: u8 = 0;
    let mut v_nativeFacets_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1164_: u8 = 0;
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: u8 = 0;
    let mut v_reuseFailAlloc_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1171_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1154_ = crate::leanh::lean_ctor_get(v_cfg_1153_, 0);
                v_srcDir_1155_ = crate::leanh::lean_ctor_get(v_cfg_1153_, 1);
                v_root_1156_ = crate::leanh::lean_ctor_get(v_cfg_1153_, 2);
                v_exeName_1157_ = crate::leanh::lean_ctor_get(v_cfg_1153_, 3);
                v_needs_1158_ = crate::leanh::lean_ctor_get(v_cfg_1153_, 4);
                v_extraDepTargets_1159_ = crate::leanh::lean_ctor_get(v_cfg_1153_, 5);
                v_supportInterpreter_1160_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1153_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1161_ = crate::leanh::lean_ctor_get(v_cfg_1153_, 6);
                v_isSharedCheck_1171_ = (!crate::leanh::lean_is_exclusive(v_cfg_1153_)) as u8;
                if v_isSharedCheck_1171_ == 0 {
                    v___x_1163_ = v_cfg_1153_;
                    v_isShared_1164_ = v_isSharedCheck_1171_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1161_);
                    crate::leanh::lean_inc(v_extraDepTargets_1159_);
                    crate::leanh::lean_inc(v_needs_1158_);
                    crate::leanh::lean_inc(v_exeName_1157_);
                    crate::leanh::lean_inc(v_root_1156_);
                    crate::leanh::lean_inc(v_srcDir_1155_);
                    crate::leanh::lean_inc(v_toLeanConfig_1154_);
                    crate::leanh::lean_dec(v_cfg_1153_);
                    v___x_1163_ = crate::leanh::lean_box(0);
                    v_isShared_1164_ = v_isSharedCheck_1171_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1165_ = crate::leanh::lean_box((v_supportInterpreter_1160_) as usize);
                v___x_1166_ = crate::leanh::lean_apply_1(v_f_1152_, v___x_1165_);
                if v_isShared_1164_ == 0 {
                    v___x_1168_ = v___x_1163_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1170_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_toLeanConfig_1154_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_srcDir_1155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_root_1156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1170_, 3, v_exeName_1157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1170_, 4, v_needs_1158_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1170_, 5, v_extraDepTargets_1159_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1170_, 6, v_nativeFacets_1161_);
                    v___x_1168_ = v_reuseFailAlloc_1170_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1169_ = (crate::leanh::lean_unbox(v___x_1166_) as u8);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1168_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v___x_1169_,
                );
                return v___x_1168_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___lam__3(
    mut v_x_1172_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1173_: u8 = 0;
    v___x_1173_ = 0;
    return v___x_1173_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___lam__3___boxed(
    mut v_x_1174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1175_: u8 = 0;
    let mut v_r_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1175_ = l_Lake_LeanExeConfig_supportInterpreter___proj___lam__3(v_x_1174_);
    crate::leanh::lean_dec_ref(v_x_1174_);
    v_r_1176_ = crate::leanh::lean_box((v_res_1175_) as usize);
    return v_r_1176_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj(
    mut v_name_1186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1187_ = l_Lake_LeanExeConfig_supportInterpreter___proj___closed__4;
    return v___x_1187_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___boxed(
    mut v_name_1188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1189_ = l_Lake_LeanExeConfig_supportInterpreter___proj(v_name_1188_);
    crate::leanh::lean_dec(v_name_1188_);
    return v_res_1189_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter_instConfigField(
    mut v_name_1190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1191_ = l_Lake_LeanExeConfig_supportInterpreter___proj(v_name_1190_);
    return v___x_1191_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter_instConfigField___boxed(
    mut v_name_1192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1193_ = l_Lake_LeanExeConfig_supportInterpreter_instConfigField(v_name_1192_);
    crate::leanh::lean_dec(v_name_1192_);
    return v_res_1193_;
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets___proj___lam__0(
    mut v_cfg_1194_: *mut crate::leanh::LeanObject,
    mut v___y_1195_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_nativeFacets_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nativeFacets_1196_ = crate::leanh::lean_ctor_get(v_cfg_1194_, 6);
    crate::leanh::lean_inc_ref(v_nativeFacets_1196_);
    crate::leanh::lean_dec_ref(v_cfg_1194_);
    v___x_1197_ = crate::leanh::lean_box((v___y_1195_) as usize);
    v___x_1198_ = crate::leanh::lean_apply_1(v_nativeFacets_1196_, v___x_1197_);
    return v___x_1198_;
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets___proj___lam__0___boxed(
    mut v_cfg_1199_: *mut crate::leanh::LeanObject,
    mut v___y_1200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_135__boxed_1201_: u8 = 0;
    let mut v_res_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_135__boxed_1201_ = (crate::leanh::lean_unbox(v___y_1200_) as u8);
    v_res_1202_ =
        l_Lake_LeanExeConfig_nativeFacets___proj___lam__0(v_cfg_1199_, v___y_135__boxed_1201_);
    return v_res_1202_;
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets___proj___lam__1(
    mut v_val_1203_: *mut crate::leanh::LeanObject,
    mut v_cfg_1204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1211_: u8 = 0;
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1214_: u8 = 0;
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1218_: u8 = 0;
    let mut v_unused_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1205_ = crate::leanh::lean_ctor_get(v_cfg_1204_, 0);
                v_srcDir_1206_ = crate::leanh::lean_ctor_get(v_cfg_1204_, 1);
                v_root_1207_ = crate::leanh::lean_ctor_get(v_cfg_1204_, 2);
                v_exeName_1208_ = crate::leanh::lean_ctor_get(v_cfg_1204_, 3);
                v_needs_1209_ = crate::leanh::lean_ctor_get(v_cfg_1204_, 4);
                v_extraDepTargets_1210_ = crate::leanh::lean_ctor_get(v_cfg_1204_, 5);
                v_supportInterpreter_1211_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1204_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_isSharedCheck_1218_ = (!crate::leanh::lean_is_exclusive(v_cfg_1204_)) as u8;
                if v_isSharedCheck_1218_ == 0 {
                    v_unused_1219_ = crate::leanh::lean_ctor_get(v_cfg_1204_, 6);
                    crate::leanh::lean_dec(v_unused_1219_);
                    v___x_1213_ = v_cfg_1204_;
                    v_isShared_1214_ = v_isSharedCheck_1218_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_extraDepTargets_1210_);
                    crate::leanh::lean_inc(v_needs_1209_);
                    crate::leanh::lean_inc(v_exeName_1208_);
                    crate::leanh::lean_inc(v_root_1207_);
                    crate::leanh::lean_inc(v_srcDir_1206_);
                    crate::leanh::lean_inc(v_toLeanConfig_1205_);
                    crate::leanh::lean_dec(v_cfg_1204_);
                    v___x_1213_ = crate::leanh::lean_box(0);
                    v_isShared_1214_ = v_isSharedCheck_1218_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1214_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1213_, 6, v_val_1203_);
                    v___x_1216_ = v___x_1213_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1217_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_toLeanConfig_1205_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_srcDir_1206_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1217_, 2, v_root_1207_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1217_, 3, v_exeName_1208_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1217_, 4, v_needs_1209_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1217_, 5, v_extraDepTargets_1210_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1217_, 6, v_val_1203_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1217_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_supportInterpreter_1211_,
                    );
                    v___x_1216_ = v_reuseFailAlloc_1217_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1216_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets___proj___lam__2(
    mut v_f_1220_: *mut crate::leanh::LeanObject,
    mut v_cfg_1221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1228_: u8 = 0;
    let mut v_nativeFacets_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1232_: u8 = 0;
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1222_ = crate::leanh::lean_ctor_get(v_cfg_1221_, 0);
                v_srcDir_1223_ = crate::leanh::lean_ctor_get(v_cfg_1221_, 1);
                v_root_1224_ = crate::leanh::lean_ctor_get(v_cfg_1221_, 2);
                v_exeName_1225_ = crate::leanh::lean_ctor_get(v_cfg_1221_, 3);
                v_needs_1226_ = crate::leanh::lean_ctor_get(v_cfg_1221_, 4);
                v_extraDepTargets_1227_ = crate::leanh::lean_ctor_get(v_cfg_1221_, 5);
                v_supportInterpreter_1228_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1221_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1229_ = crate::leanh::lean_ctor_get(v_cfg_1221_, 6);
                v_isSharedCheck_1237_ = (!crate::leanh::lean_is_exclusive(v_cfg_1221_)) as u8;
                if v_isSharedCheck_1237_ == 0 {
                    v___x_1231_ = v_cfg_1221_;
                    v_isShared_1232_ = v_isSharedCheck_1237_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1229_);
                    crate::leanh::lean_inc(v_extraDepTargets_1227_);
                    crate::leanh::lean_inc(v_needs_1226_);
                    crate::leanh::lean_inc(v_exeName_1225_);
                    crate::leanh::lean_inc(v_root_1224_);
                    crate::leanh::lean_inc(v_srcDir_1223_);
                    crate::leanh::lean_inc(v_toLeanConfig_1222_);
                    crate::leanh::lean_dec(v_cfg_1221_);
                    v___x_1231_ = crate::leanh::lean_box(0);
                    v_isShared_1232_ = v_isSharedCheck_1237_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1233_ = crate::leanh::lean_apply_1(v_f_1220_, v_nativeFacets_1229_);
                if v_isShared_1232_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1231_, 6, v___x_1233_);
                    v___x_1235_ = v___x_1231_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1236_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_toLeanConfig_1222_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_srcDir_1223_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 2, v_root_1224_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 3, v_exeName_1225_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 4, v_needs_1226_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 5, v_extraDepTargets_1227_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 6, v___x_1233_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1236_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_supportInterpreter_1228_,
                    );
                    v___x_1235_ = v_reuseFailAlloc_1236_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets___proj___lam__3(
    mut v_x_1238_: *mut crate::leanh::LeanObject,
    mut v___y_1239_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_1239_ == 0 {
                    v___x_1245_ = l_Lake_Module_oFacet;
                    v___y_1241_ = v___x_1245_;
                    state = 1;
                    continue;
                } else {
                    v___x_1246_ = l_Lake_Module_oExportFacet;
                    v___y_1241_ = v___x_1246_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1242_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1243_ = lean_mk_empty_array_with_capacity(v___x_1242_);
                crate::leanh::lean_inc(v___y_1241_);
                v___x_1244_ = lean_array_push(v___x_1243_, v___y_1241_);
                return v___x_1244_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets___proj___lam__3___boxed(
    mut v_x_1247_: *mut crate::leanh::LeanObject,
    mut v___y_1248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_185__boxed_1249_: u8 = 0;
    let mut v_res_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_185__boxed_1249_ = (crate::leanh::lean_unbox(v___y_1248_) as u8);
    v_res_1250_ =
        l_Lake_LeanExeConfig_nativeFacets___proj___lam__3(v_x_1247_, v___y_185__boxed_1249_);
    crate::leanh::lean_dec_ref(v_x_1247_);
    return v_res_1250_;
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets___proj(
    mut v_name_1260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1261_ = l_Lake_LeanExeConfig_nativeFacets___proj___closed__4;
    return v___x_1261_;
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets___proj___boxed(
    mut v_name_1262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1263_ = l_Lake_LeanExeConfig_nativeFacets___proj(v_name_1262_);
    crate::leanh::lean_dec(v_name_1262_);
    return v_res_1263_;
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets_instConfigField(
    mut v_name_1264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1265_ = l_Lake_LeanExeConfig_nativeFacets___proj(v_name_1264_);
    return v___x_1265_;
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets_instConfigField___boxed(
    mut v_name_1266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1267_ = l_Lake_LeanExeConfig_nativeFacets_instConfigField(v_name_1266_);
    crate::leanh::lean_dec(v_name_1266_);
    return v_res_1267_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig___proj___lam__0(
    mut v_cfg_1268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toLeanConfig_1269_ = crate::leanh::lean_ctor_get(v_cfg_1268_, 0);
    crate::leanh::lean_inc_ref(v_toLeanConfig_1269_);
    return v_toLeanConfig_1269_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig___proj___lam__0___boxed(
    mut v_cfg_1270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1271_ = l_Lake_LeanExeConfig_toLeanConfig___proj___lam__0(v_cfg_1270_);
    crate::leanh::lean_dec_ref(v_cfg_1270_);
    return v_res_1271_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig___proj___lam__1(
    mut v_val_1272_: *mut crate::leanh::LeanObject,
    mut v_cfg_1273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_srcDir_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1279_: u8 = 0;
    let mut v_nativeFacets_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1283_: u8 = 0;
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1287_: u8 = 0;
    let mut v_unused_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_srcDir_1274_ = crate::leanh::lean_ctor_get(v_cfg_1273_, 1);
                v_root_1275_ = crate::leanh::lean_ctor_get(v_cfg_1273_, 2);
                v_exeName_1276_ = crate::leanh::lean_ctor_get(v_cfg_1273_, 3);
                v_needs_1277_ = crate::leanh::lean_ctor_get(v_cfg_1273_, 4);
                v_extraDepTargets_1278_ = crate::leanh::lean_ctor_get(v_cfg_1273_, 5);
                v_supportInterpreter_1279_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1273_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1280_ = crate::leanh::lean_ctor_get(v_cfg_1273_, 6);
                v_isSharedCheck_1287_ = (!crate::leanh::lean_is_exclusive(v_cfg_1273_)) as u8;
                if v_isSharedCheck_1287_ == 0 {
                    v_unused_1288_ = crate::leanh::lean_ctor_get(v_cfg_1273_, 0);
                    crate::leanh::lean_dec(v_unused_1288_);
                    v___x_1282_ = v_cfg_1273_;
                    v_isShared_1283_ = v_isSharedCheck_1287_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1280_);
                    crate::leanh::lean_inc(v_extraDepTargets_1278_);
                    crate::leanh::lean_inc(v_needs_1277_);
                    crate::leanh::lean_inc(v_exeName_1276_);
                    crate::leanh::lean_inc(v_root_1275_);
                    crate::leanh::lean_inc(v_srcDir_1274_);
                    crate::leanh::lean_dec(v_cfg_1273_);
                    v___x_1282_ = crate::leanh::lean_box(0);
                    v_isShared_1283_ = v_isSharedCheck_1287_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1283_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1282_, 0, v_val_1272_);
                    v___x_1285_ = v___x_1282_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1286_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_val_1272_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_srcDir_1274_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 2, v_root_1275_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 3, v_exeName_1276_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 4, v_needs_1277_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 5, v_extraDepTargets_1278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 6, v_nativeFacets_1280_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1286_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_supportInterpreter_1279_,
                    );
                    v___x_1285_ = v_reuseFailAlloc_1286_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig___proj___lam__2(
    mut v_f_1289_: *mut crate::leanh::LeanObject,
    mut v_cfg_1290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLeanConfig_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1297_: u8 = 0;
    let mut v_nativeFacets_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1301_: u8 = 0;
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1306_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1291_ = crate::leanh::lean_ctor_get(v_cfg_1290_, 0);
                v_srcDir_1292_ = crate::leanh::lean_ctor_get(v_cfg_1290_, 1);
                v_root_1293_ = crate::leanh::lean_ctor_get(v_cfg_1290_, 2);
                v_exeName_1294_ = crate::leanh::lean_ctor_get(v_cfg_1290_, 3);
                v_needs_1295_ = crate::leanh::lean_ctor_get(v_cfg_1290_, 4);
                v_extraDepTargets_1296_ = crate::leanh::lean_ctor_get(v_cfg_1290_, 5);
                v_supportInterpreter_1297_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_1290_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1298_ = crate::leanh::lean_ctor_get(v_cfg_1290_, 6);
                v_isSharedCheck_1306_ = (!crate::leanh::lean_is_exclusive(v_cfg_1290_)) as u8;
                if v_isSharedCheck_1306_ == 0 {
                    v___x_1300_ = v_cfg_1290_;
                    v_isShared_1301_ = v_isSharedCheck_1306_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nativeFacets_1298_);
                    crate::leanh::lean_inc(v_extraDepTargets_1296_);
                    crate::leanh::lean_inc(v_needs_1295_);
                    crate::leanh::lean_inc(v_exeName_1294_);
                    crate::leanh::lean_inc(v_root_1293_);
                    crate::leanh::lean_inc(v_srcDir_1292_);
                    crate::leanh::lean_inc(v_toLeanConfig_1291_);
                    crate::leanh::lean_dec(v_cfg_1290_);
                    v___x_1300_ = crate::leanh::lean_box(0);
                    v_isShared_1301_ = v_isSharedCheck_1306_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1302_ = crate::leanh::lean_apply_1(v_f_1289_, v_toLeanConfig_1291_);
                if v_isShared_1301_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1300_, 0, v___x_1302_);
                    v___x_1304_ = v___x_1300_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1305_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_srcDir_1292_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 2, v_root_1293_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 3, v_exeName_1294_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 4, v_needs_1295_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 5, v_extraDepTargets_1296_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 6, v_nativeFacets_1298_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1305_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_supportInterpreter_1297_,
                    );
                    v___x_1304_ = v_reuseFailAlloc_1305_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1304_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3(
    mut v_x_1314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1315_ = l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__1;
    return v___x_1315_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___boxed(
    mut v_x_1316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1317_ = l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3(v_x_1316_);
    crate::leanh::lean_dec_ref(v_x_1316_);
    return v_res_1317_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig___proj(
    mut v_name_1327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1328_ = l_Lake_LeanExeConfig_toLeanConfig___proj___closed__4;
    return v___x_1328_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig___proj___boxed(
    mut v_name_1329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1330_ = l_Lake_LeanExeConfig_toLeanConfig___proj(v_name_1329_);
    crate::leanh::lean_dec(v_name_1329_);
    return v_res_1330_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig_instConfigParent(
    mut v_name_1331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1332_ = l_Lake_LeanExeConfig_toLeanConfig___proj(v_name_1331_);
    return v___x_1332_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig_instConfigParent___boxed(
    mut v_name_1333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1334_ = l_Lake_LeanExeConfig_toLeanConfig_instConfigParent(v_name_1333_);
    crate::leanh::lean_dec(v_name_1333_);
    return v_res_1334_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1344_ = l_Lake_LeanExeConfig___fields___closed__3;
    v___x_1345_ = l_Lake_LeanExeConfig___fields___closed__0;
    v___x_1346_ = lean_array_push(v___x_1345_, v___x_1344_);
    return v___x_1346_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1354_ = l_Lake_LeanExeConfig___fields___closed__7;
    v___x_1355_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__4),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__4_once),
        _init_l_Lake_LeanExeConfig___fields___closed__4,
    );
    v___x_1356_ = lean_array_push(v___x_1355_, v___x_1354_);
    return v___x_1356_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1364_ = l_Lake_LeanExeConfig___fields___closed__11;
    v___x_1365_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__8),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__8_once),
        _init_l_Lake_LeanExeConfig___fields___closed__8,
    );
    v___x_1366_ = lean_array_push(v___x_1365_, v___x_1364_);
    return v___x_1366_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__16() -> *mut crate::leanh::LeanObject {
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1374_ = l_Lake_LeanExeConfig___fields___closed__15;
    v___x_1375_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__12),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__12_once),
        _init_l_Lake_LeanExeConfig___fields___closed__12,
    );
    v___x_1376_ = lean_array_push(v___x_1375_, v___x_1374_);
    return v___x_1376_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__20() -> *mut crate::leanh::LeanObject {
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1384_ = l_Lake_LeanExeConfig___fields___closed__19;
    v___x_1385_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__16),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__16_once),
        _init_l_Lake_LeanExeConfig___fields___closed__16,
    );
    v___x_1386_ = lean_array_push(v___x_1385_, v___x_1384_);
    return v___x_1386_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__24() -> *mut crate::leanh::LeanObject {
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1394_ = l_Lake_LeanExeConfig___fields___closed__23;
    v___x_1395_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__20),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__20_once),
        _init_l_Lake_LeanExeConfig___fields___closed__20,
    );
    v___x_1396_ = lean_array_push(v___x_1395_, v___x_1394_);
    return v___x_1396_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__28() -> *mut crate::leanh::LeanObject {
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1404_ = l_Lake_LeanExeConfig___fields___closed__27;
    v___x_1405_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__24),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__24_once),
        _init_l_Lake_LeanExeConfig___fields___closed__24,
    );
    v___x_1406_ = lean_array_push(v___x_1405_, v___x_1404_);
    return v___x_1406_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__29() -> *mut crate::leanh::LeanObject {
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1407_ = l_Lake_LeanConfig___fields;
    v___x_1408_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__28),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__28_once),
        _init_l_Lake_LeanExeConfig___fields___closed__28,
    );
    v___x_1409_ = l_Array_append___redArg(v___x_1408_, v___x_1407_);
    return v___x_1409_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__33() -> *mut crate::leanh::LeanObject {
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1417_ = l_Lake_LeanExeConfig___fields___closed__32;
    v___x_1418_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__29),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__29_once),
        _init_l_Lake_LeanExeConfig___fields___closed__29,
    );
    v___x_1419_ = lean_array_push(v___x_1418_, v___x_1417_);
    return v___x_1419_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields() -> *mut crate::leanh::LeanObject {
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1420_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__33),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__33_once),
        _init_l_Lake_LeanExeConfig___fields___closed__33,
    );
    return v___x_1420_;
}
pub unsafe fn l_Lake_LeanExeConfig_instConfigFields(
    mut v_name_1421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1422_ = l_Lake_LeanExeConfig___fields;
    return v___x_1422_;
}
pub unsafe fn l_Lake_LeanExeConfig_instConfigFields___boxed(
    mut v_name_1423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1424_ = l_Lake_LeanExeConfig_instConfigFields(v_name_1423_);
    crate::leanh::lean_dec(v_name_1423_);
    return v_res_1424_;
}
pub unsafe fn l_Lake_LeanExeConfig_instConfigInfo___lam__0(
    mut v_x1_1425_: *mut crate::leanh::LeanObject,
    mut v_x2_1426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1427_ = crate::leanh::lean_ctor_get(v_x2_1426_, 0);
    crate::leanh::lean_inc(v_name_1427_);
    v___x_1428_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_name_1427_,
        v_x2_1426_,
        v_x1_1425_,
    );
    return v___x_1428_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig_instConfigInfo___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1429_ = l_Lake_LeanExeConfig___fields;
    v___x_1430_ = lean_array_get_size(v___x_1429_);
    return v___x_1430_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig_instConfigInfo___closed__11() -> u8 {
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: u8 = 0;
    v___x_1450_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_LeanExeConfig_instConfigInfo___closed__0,
    );
    v___x_1451_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1452_ = lean_nat_dec_lt(v___x_1451_, v___x_1450_);
    return v___x_1452_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig_instConfigInfo___closed__13() -> u8 {
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: u8 = 0;
    v___x_1454_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_LeanExeConfig_instConfigInfo___closed__0,
    );
    v___x_1455_ = lean_nat_dec_le(v___x_1454_, v___x_1454_);
    return v___x_1455_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig_instConfigInfo___closed__14() -> usize {
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: usize = 0;
    v___x_1456_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_LeanExeConfig_instConfigInfo___closed__0,
    );
    v___x_1457_ = lean_usize_of_nat(v___x_1456_);
    return v___x_1457_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig_instConfigInfo___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: usize = 0;
    let mut v___x_1460_: usize = 0;
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1458_ = crate::leanh::lean_box(1);
    v___x_1459_ = crate::leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__14),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__14_once),
        _init_l_Lake_LeanExeConfig_instConfigInfo___closed__14,
    );
    v___x_1460_ = 0usize;
    v___x_1461_ = l_Lake_LeanExeConfig___fields;
    v___f_1462_ = l_Lake_LeanExeConfig_instConfigInfo___closed__12;
    v___x_1463_ = l_Lake_LeanExeConfig_instConfigInfo___closed__10;
    v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1463_,
        v___f_1462_,
        v___x_1461_,
        v___x_1460_,
        v___x_1459_,
        v___x_1458_,
    );
    return v___x_1464_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig_instConfigInfo() -> *mut crate::leanh::LeanObject {
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: u8 = 0;
    let mut v___x_1472_: u8 = 0;
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1465_ = l_Lake_LeanExeConfig___fields;
                v___x_1470_ = crate::leanh::lean_box(1);
                v___x_1471_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__11),
                    core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__11_once),
                    _init_l_Lake_LeanExeConfig_instConfigInfo___closed__11,
                );
                if v___x_1471_ == 0 {
                    v___y_1467_ = v___x_1470_;
                    state = 1;
                    continue;
                } else {
                    v___x_1472_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__13),
                        core::ptr::addr_of_mut!(
                            l_Lake_LeanExeConfig_instConfigInfo___closed__13_once
                        ),
                        _init_l_Lake_LeanExeConfig_instConfigInfo___closed__13,
                    );
                    if v___x_1472_ == 0 {
                        if v___x_1471_ == 0 {
                            v___y_1467_ = v___x_1470_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1473_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lake_LeanExeConfig_instConfigInfo___closed__15
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lake_LeanExeConfig_instConfigInfo___closed__15_once
                                ),
                                _init_l_Lake_LeanExeConfig_instConfigInfo___closed__15,
                            );
                            v___y_1467_ = v___x_1473_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1474_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lake_LeanExeConfig_instConfigInfo___closed__15
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lake_LeanExeConfig_instConfigInfo___closed__15_once
                            ),
                            _init_l_Lake_LeanExeConfig_instConfigInfo___closed__15,
                        );
                        v___y_1467_ = v___x_1474_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1468_ = crate::leanh::lean_unsigned_to_nat(1);
                crate::leanh::lean_inc(v___y_1467_);
                v___x_1469_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1469_, 0, v___x_1465_);
                crate::leanh::lean_ctor_set(v___x_1469_, 1, v___y_1467_);
                crate::leanh::lean_ctor_set(v___x_1469_, 2, v___x_1468_);
                return v___x_1469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_instEmptyCollection___lam__1(
    mut v___x_1475_: u8,
    mut v_x_1476_: *mut crate::leanh::LeanObject,
) -> u8 {
    return v___x_1475_;
}
pub unsafe fn l_Lake_LeanExeConfig_instEmptyCollection___lam__1___boxed(
    mut v___x_1477_: *mut crate::leanh::LeanObject,
    mut v_x_1478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_83__boxed_1479_: u8 = 0;
    let mut v_res_1480_: u8 = 0;
    let mut v_r_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_83__boxed_1479_ = (crate::leanh::lean_unbox(v___x_1477_) as u8);
    v_res_1480_ =
        l_Lake_LeanExeConfig_instEmptyCollection___lam__1(v___x_83__boxed_1479_, v_x_1478_);
    crate::leanh::lean_dec_ref(v_x_1478_);
    v_r_1481_ = crate::leanh::lean_box((v_res_1480_) as usize);
    return v_r_1481_;
}
pub unsafe fn l_Lake_LeanExeConfig_instEmptyCollection(
    mut v_name_1485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: u8 = 0;
    let mut v___f_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1486_ = l_Lake_instInhabitedLeanExeConfig_default___closed__0;
    v___x_1487_ = l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0;
    v___x_1488_ = l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__1;
    v___x_1489_ = l_Lake_instInhabitedLeanExeConfig_default___closed__1;
    v___x_1490_ = l_Lake_instInhabitedLeanExeConfig_default___closed__2;
    v___x_1491_ = 0;
    v___f_1492_ = l_Lake_LeanExeConfig_instEmptyCollection___closed__0;
    crate::leanh::lean_inc(v_name_1485_);
    v___x_1493_ = l_Lean_Name_toStringWithSep(v___x_1490_, v___x_1491_, v_name_1485_, v___f_1492_);
    v___x_1494_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1494_, 0, v___x_1488_);
    crate::leanh::lean_ctor_set(v___x_1494_, 1, v___x_1489_);
    crate::leanh::lean_ctor_set(v___x_1494_, 2, v_name_1485_);
    crate::leanh::lean_ctor_set(v___x_1494_, 3, v___x_1493_);
    crate::leanh::lean_ctor_set(v___x_1494_, 4, v___x_1487_);
    crate::leanh::lean_ctor_set(v___x_1494_, 5, v___x_1487_);
    crate::leanh::lean_ctor_set(v___x_1494_, 6, v___f_1486_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1494_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
        v___x_1491_,
    );
    return v___x_1494_;
}
pub unsafe fn l_Lake_LeanExeConfig_name___redArg(
    mut v_n_1495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_n_1495_);
    return v_n_1495_;
}
pub unsafe fn l_Lake_LeanExeConfig_name___redArg___boxed(
    mut v_n_1496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1497_ = l_Lake_LeanExeConfig_name___redArg(v_n_1496_);
    crate::leanh::lean_dec(v_n_1496_);
    return v_res_1497_;
}
pub unsafe fn l_Lake_LeanExeConfig_name(
    mut v_n_1498_: *mut crate::leanh::LeanObject,
    mut v_x_1499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_n_1498_);
    return v_n_1498_;
}
pub unsafe fn l_Lake_LeanExeConfig_name___boxed(
    mut v_n_1500_: *mut crate::leanh::LeanObject,
    mut v_x_1501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1502_ = l_Lake_LeanExeConfig_name(v_n_1500_, v_x_1501_);
    crate::leanh::lean_dec_ref(v_x_1501_);
    crate::leanh::lean_dec(v_n_1500_);
    return v_res_1502_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_LeanExeConfig(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
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
    res = runtime_initialize_Lake_Config_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lake_LeanExeConfig___fields = _init_l_Lake_LeanExeConfig___fields();
    crate::leanh::lean_mark_persistent(l_Lake_LeanExeConfig___fields);
    l_Lake_LeanExeConfig_instConfigInfo = _init_l_Lake_LeanExeConfig_instConfigInfo();
    crate::leanh::lean_mark_persistent(l_Lake_LeanExeConfig_instConfigInfo);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_LeanExeConfig(
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
pub unsafe fn initialize_Lake_Config_LeanExeConfig(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
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
    res = runtime_initialize_Lake_Config_LeanExeConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_LeanExeConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Config_LeanExeConfig(builtin);
}
