// Lean compiler output
// Module: Lake.Config.LeanExeConfig
// Imports: Lake.Build.Facets Lake.Config.LeanConfig Lake.Config.Meta Lake.Config.Meta
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
    lean_nat_dec_lt, lean_string_append, lean_usize_of_nat,
};
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
pub static l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0___closed__0_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [91, 97, 110, 111, 110, 121, 109, 111, 117, 115, 93, 0]};
static mut l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedLeanExeConfig_default___closed__0_value:
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
    m_fun: l_Lake_instInhabitedLeanExeConfig_default___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instInhabitedLeanExeConfig_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanExeConfig_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedLeanExeConfig_default___closed__1_value:
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
    m_data: [46, 0],
};
static mut l_Lake_instInhabitedLeanExeConfig_default___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanExeConfig_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedLeanExeConfig_default___closed__2_value:
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
    m_data: [45, 0],
};
static mut l_Lake_instInhabitedLeanExeConfig_default___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanExeConfig_default___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedLeanExeConfig_default___closed__3_value:
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
static mut l_Lake_instInhabitedLeanExeConfig_default___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanExeConfig_default___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_srcDir___proj___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanExeConfig_srcDir___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_srcDir___proj___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_srcDir___proj___closed__1_value: leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanExeConfig_srcDir___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_srcDir___proj___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_srcDir___proj___closed__2_value: leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanExeConfig_srcDir___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_srcDir___proj___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_srcDir___proj___closed__3_value: leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanExeConfig_srcDir___proj___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_srcDir___proj___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_srcDir___proj___closed__4_value: leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig_srcDir___proj___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_root___proj___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_root___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_root___proj___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_root___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_root___proj___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_root___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_root___proj___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_root___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_root___proj___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_root___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_root___proj___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_root___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_exeName___proj___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanExeConfig_exeName___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_exeName___proj___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_exeName___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_exeName___proj___closed__1_value: leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanExeConfig_exeName___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_exeName___proj___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_exeName___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_exeName___proj___closed__2_value: leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanExeConfig_exeName___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_exeName___proj___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_exeName___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_needs___proj___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_needs___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_needs___proj___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_needs___proj___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_needs___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_needs___proj___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_needs___proj___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_needs___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_needs___proj___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_needs___proj___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_needs___proj___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_needs___proj___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_needs___proj___closed__4_value: leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig_needs___proj___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_extraDepTargets___proj___lam__3___closed__0_value:
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
static mut l_Lake_LeanExeConfig_extraDepTargets___proj___lam__3___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___lam__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_extraDepTargets___proj___closed__0_value:
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
    m_fun: l_Lake_LeanExeConfig_extraDepTargets___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_extraDepTargets___proj___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_extraDepTargets___proj___closed__1_value:
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
    m_fun: l_Lake_LeanExeConfig_extraDepTargets___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_extraDepTargets___proj___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_extraDepTargets___proj___closed__2_value:
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
    m_fun: l_Lake_LeanExeConfig_extraDepTargets___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_extraDepTargets___proj___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_extraDepTargets___proj___closed__3_value:
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
    m_fun: l_Lake_LeanExeConfig_extraDepTargets___proj___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_extraDepTargets___proj___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_extraDepTargets___proj___closed__4_value:
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
        core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig_extraDepTargets___proj___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_supportInterpreter___proj___closed__0_value:
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
    m_fun: l_Lake_LeanExeConfig_supportInterpreter___proj___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_supportInterpreter___proj___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_supportInterpreter___proj___closed__1_value:
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
    m_fun: l_Lake_LeanExeConfig_supportInterpreter___proj___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_supportInterpreter___proj___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_supportInterpreter___proj___closed__2_value:
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
    m_fun: l_Lake_LeanExeConfig_supportInterpreter___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_supportInterpreter___proj___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_supportInterpreter___proj___closed__3_value:
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
    m_fun: l_Lake_LeanExeConfig_supportInterpreter___proj___lam__3___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_supportInterpreter___proj___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_supportInterpreter___proj___closed__4_value:
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
        core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig_supportInterpreter___proj___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_nativeFacets___proj___closed__0_value:
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
    m_fun: l_Lake_LeanExeConfig_nativeFacets___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_nativeFacets___proj___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_nativeFacets___proj___closed__1_value:
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
    m_fun: l_Lake_LeanExeConfig_nativeFacets___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_nativeFacets___proj___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_nativeFacets___proj___closed__2_value:
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
    m_fun: l_Lake_LeanExeConfig_nativeFacets___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_nativeFacets___proj___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_nativeFacets___proj___closed__3_value:
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
    m_fun: l_Lake_LeanExeConfig_nativeFacets___proj___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_nativeFacets___proj___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_nativeFacets___proj___closed__4_value:
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
        core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig_nativeFacets___proj___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value:
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
static mut l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__1_value:
    leanh::LeanCtorObject<14> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 13
            + 8) as u16,
        other: 13,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
            as *mut leanh::LeanObject,
        515 as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_toLeanConfig___proj___closed__0_value:
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
    m_fun: l_Lake_LeanExeConfig_toLeanConfig___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_toLeanConfig___proj___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_toLeanConfig___proj___closed__1_value:
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
    m_fun: l_Lake_LeanExeConfig_toLeanConfig___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_toLeanConfig___proj___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_toLeanConfig___proj___closed__2_value:
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
    m_fun: l_Lake_LeanExeConfig_toLeanConfig___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_toLeanConfig___proj___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_toLeanConfig___proj___closed__3_value:
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
    m_fun: l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_toLeanConfig___proj___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_toLeanConfig___proj___closed__4_value:
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
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig_toLeanConfig___proj___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_Lake_LeanExeConfig___fields___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__1_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_LeanExeConfig___fields___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__1_value)
                as *mut leanh::LeanObject,
            10458569134091399506 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__2_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig___fields___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanExeConfig___fields___closed__5_value: leanh::LeanStringObject<5> =
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
        m_data: [114, 111, 111, 116, 0],
    };
static mut l_Lake_LeanExeConfig___fields___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__5_value)
                as *mut leanh::LeanObject,
            13952697477363952342 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__6_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig___fields___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanExeConfig___fields___closed__9_value: leanh::LeanStringObject<8> =
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
        m_data: [101, 120, 101, 78, 97, 109, 101, 0],
    };
static mut l_Lake_LeanExeConfig___fields___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__10_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__9_value)
                as *mut leanh::LeanObject,
            535955292391232655 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__11_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__10_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__10_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig___fields___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanExeConfig___fields___closed__13_value: leanh::LeanStringObject<6> =
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
        m_data: [110, 101, 101, 100, 115, 0],
    };
static mut l_Lake_LeanExeConfig___fields___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__14_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__13_value)
                as *mut leanh::LeanObject,
            14359248566632897495 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__15_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__14_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__14_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__15_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig___fields___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanExeConfig___fields___closed__17_value: leanh::LeanStringObject<16> =
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
            101, 120, 116, 114, 97, 68, 101, 112, 84, 97, 114, 103, 101, 116, 115, 0,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__18_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__17_value)
                as *mut leanh::LeanObject,
            376106234249747944 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__19_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__18_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__18_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__19_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig___fields___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanExeConfig___fields___closed__21_value: leanh::LeanStringObject<19> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_LeanExeConfig___fields___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__22_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__21_value)
                as *mut leanh::LeanObject,
            3358201691291746559 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__23_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__22_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__22_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__23_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig___fields___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanExeConfig___fields___closed__25_value: leanh::LeanStringObject<13> =
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
        m_data: [110, 97, 116, 105, 118, 101, 70, 97, 99, 101, 116, 115, 0],
    };
static mut l_Lake_LeanExeConfig___fields___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__26_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__25_value)
                as *mut leanh::LeanObject,
            2134236907718250370 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__26_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__27_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__26_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__26_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__27_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__28_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig___fields___closed__28: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_LeanExeConfig___fields___closed__29_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig___fields___closed__29: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanExeConfig___fields___closed__30_value: leanh::LeanStringObject<13> =
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
        m_data: [116, 111, 76, 101, 97, 110, 67, 111, 110, 102, 105, 103, 0],
    };
static mut l_Lake_LeanExeConfig___fields___closed__30: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__30_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__31_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__30_value)
                as *mut leanh::LeanObject,
            782171420137495241 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__31: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__31_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__32_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__31_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__31_value)
                as *mut leanh::LeanObject,
            256 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__32_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__33_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig___fields___closed__33: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_LeanExeConfig___fields: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__1_value: leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__2_value: leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__3_value: leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__4_value: leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__5_value: leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__6_value: leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__7_value: leanh::LeanClosureObject<
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__8_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__9_value: leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__10_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__11: u8 = 0;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__12_value: leanh::LeanClosureObject<
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
    m_fun: l_Lake_LeanExeConfig_instConfigInfo___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__13: u8 = 0;
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__14: usize = 0;
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_LeanExeConfig_instConfigInfo: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanExeConfig_instEmptyCollection___closed__0_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanExeConfig_instEmptyCollection___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lake_LeanExeConfig_instEmptyCollection___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instEmptyCollection___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_instInhabitedLeanExeConfig_default___lam__0(
    mut v_shouldExport_752_: u8,
) -> *mut leanh::LeanObject {
    let mut v___y_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                v___x_755_ = leanh::lean_unsigned_to_nat(1);
                v___x_756_ = lean_mk_empty_array_with_capacity(v___x_755_);
                leanh::lean_inc(v___y_754_);
                v___x_757_ = lean_array_push(v___x_756_, v___y_754_);
                return v___x_757_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instInhabitedLeanExeConfig_default___lam__0___boxed(
    mut v_shouldExport_760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_shouldExport_boxed_761_: u8 = 0;
    let mut v_res_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_shouldExport_boxed_761_ = (leanh::lean_unbox(v_shouldExport_760_) as u8);
    v_res_762_ = l_Lake_instInhabitedLeanExeConfig_default___lam__0(v_shouldExport_boxed_761_);
    return v_res_762_;
}
pub unsafe fn l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0(
    mut v_sep_764_: *mut leanh::LeanObject,
    mut v_escape_765_: u8,
    mut v_n_766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_n_766_) {
        0 => {
            let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_767_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0___closed__0;
            return v___x_767_;
        }
        1 => {
            let mut v_pre_768_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_pre_768_ = leanh::lean_ctor_get(v_n_766_, 0);
            if leanh::lean_obj_tag(v_pre_768_) == 0 {
                let mut v_str_769_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_770_: u8 = 0;
                let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_str_769_ = leanh::lean_ctor_get(v_n_766_, 1);
                leanh::lean_inc_ref(v_str_769_);
                leanh::lean_dec_ref_known(v_n_766_, 2);
                v___x_770_ = 0;
                v___x_771_ =
                    l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(
                        v_escape_765_,
                        v_str_769_,
                        v___x_770_,
                    );
                return v___x_771_;
            } else {
                let mut v_str_772_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_r_773_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_775_: u8 = 0;
                let mut v___x_776_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_r_x27_777_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc(v_pre_768_);
                v_str_772_ = leanh::lean_ctor_get(v_n_766_, 1);
                leanh::lean_inc_ref(v_str_772_);
                leanh::lean_dec_ref_known(v_n_766_, 2);
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
                leanh::lean_dec_ref(v___x_776_);
                return v_r_x27_777_;
            }
        }
        _ => {
            let mut v_pre_778_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_pre_778_ = leanh::lean_ctor_get(v_n_766_, 0);
            if leanh::lean_obj_tag(v_pre_778_) == 0 {
                let mut v_i_779_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_i_779_ = leanh::lean_ctor_get(v_n_766_, 1);
                leanh::lean_inc(v_i_779_);
                leanh::lean_dec_ref_known(v_n_766_, 2);
                v___x_780_ = l_Nat_reprFast(v_i_779_);
                return v___x_780_;
            } else {
                let mut v_i_781_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_782_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_783_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_784_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_785_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc(v_pre_778_);
                v_i_781_ = leanh::lean_ctor_get(v_n_766_, 1);
                leanh::lean_inc(v_i_781_);
                leanh::lean_dec_ref_known(v_n_766_, 2);
                v___x_782_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0(v_sep_764_, v_escape_765_, v_pre_778_);
                v___x_783_ = lean_string_append(v___x_782_, v_sep_764_);
                v___x_784_ = l_Nat_reprFast(v_i_781_);
                v___x_785_ = lean_string_append(v___x_783_, v___x_784_);
                leanh::lean_dec_ref(v___x_784_);
                return v___x_785_;
            }
        }
    }
}
pub unsafe fn l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0___boxed(
    mut v_sep_786_: *mut leanh::LeanObject,
    mut v_escape_787_: *mut leanh::LeanObject,
    mut v_n_788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_escape_boxed_789_: u8 = 0;
    let mut v_res_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_escape_boxed_789_ = (leanh::lean_unbox(v_escape_787_) as u8);
    v_res_790_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0(v_sep_786_, v_escape_boxed_789_, v_n_788_);
    leanh::lean_dec_ref(v_sep_786_);
    return v_res_790_;
}
pub unsafe fn l_Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0(
    mut v_sep_791_: *mut leanh::LeanObject,
    mut v_escape_792_: u8,
    mut v_n_793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_n_793_) {
        0 => {
            let mut v___x_794_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_794_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0___closed__0;
            return v___x_794_;
        }
        1 => {
            let mut v_pre_795_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_str_796_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_797_: u8 = 0;
            v_pre_795_ = leanh::lean_ctor_get(v_n_793_, 0);
            leanh::lean_inc(v_pre_795_);
            v_str_796_ = leanh::lean_ctor_get(v_n_793_, 1);
            leanh::lean_inc_ref(v_str_796_);
            leanh::lean_dec_ref_known(v_n_793_, 2);
            v___x_797_ = 0;
            if leanh::lean_obj_tag(v_pre_795_) == 0 {
                let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_798_ =
                    l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(
                        v_escape_792_,
                        v_str_796_,
                        v___x_797_,
                    );
                return v___x_798_;
            } else {
                let mut v_r_799_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_801_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_r_x27_802_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_r_799_ = l_Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0(v_sep_791_, v_escape_792_, v_pre_795_);
                v___x_800_ = lean_string_append(v_r_799_, v_sep_791_);
                v___x_801_ =
                    l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(
                        v_escape_792_,
                        v_str_796_,
                        v___x_797_,
                    );
                v_r_x27_802_ = lean_string_append(v___x_800_, v___x_801_);
                leanh::lean_dec_ref(v___x_801_);
                return v_r_x27_802_;
            }
        }
        _ => {
            let mut v_pre_803_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_pre_803_ = leanh::lean_ctor_get(v_n_793_, 0);
            if leanh::lean_obj_tag(v_pre_803_) == 0 {
                let mut v_i_804_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_i_804_ = leanh::lean_ctor_get(v_n_793_, 1);
                leanh::lean_inc(v_i_804_);
                leanh::lean_dec_ref_known(v_n_793_, 2);
                v___x_805_ = l_Nat_reprFast(v_i_804_);
                return v___x_805_;
            } else {
                let mut v_i_806_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_807_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_808_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_809_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_810_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_inc(v_pre_803_);
                v_i_806_ = leanh::lean_ctor_get(v_n_793_, 1);
                leanh::lean_inc(v_i_806_);
                leanh::lean_dec_ref_known(v_n_793_, 2);
                v___x_807_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0(v_sep_791_, v_escape_792_, v_pre_803_);
                v___x_808_ = lean_string_append(v___x_807_, v_sep_791_);
                v___x_809_ = l_Nat_reprFast(v_i_806_);
                v___x_810_ = lean_string_append(v___x_808_, v___x_809_);
                leanh::lean_dec_ref(v___x_809_);
                return v___x_810_;
            }
        }
    }
}
pub unsafe fn l_Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0___boxed(
    mut v_sep_811_: *mut leanh::LeanObject,
    mut v_escape_812_: *mut leanh::LeanObject,
    mut v_n_813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_escape_boxed_814_: u8 = 0;
    let mut v_res_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_escape_boxed_814_ = (leanh::lean_unbox(v_escape_812_) as u8);
    v_res_815_ =
        l_Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0(
            v_sep_811_,
            v_escape_boxed_814_,
            v_n_813_,
        );
    leanh::lean_dec_ref(v_sep_811_);
    return v_res_815_;
}
pub unsafe fn l_Lake_instInhabitedLeanExeConfig_default(
    mut v_name_821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: u8 = 0;
    let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_822_ = l_Lake_instInhabitedLeanExeConfig_default___closed__0;
    v___x_823_ = l_Lake_instInhabitedLeanConfig_default;
    v___x_824_ = l_Lake_instInhabitedLeanExeConfig_default___closed__1;
    v___x_825_ = l_Lake_instInhabitedLeanExeConfig_default___closed__2;
    v___x_826_ = 0;
    leanh::lean_inc(v_name_821_);
    v___x_827_ =
        l_Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0(
            v___x_825_,
            v___x_826_,
            v_name_821_,
        );
    v___x_828_ = l_Lake_instInhabitedLeanExeConfig_default___closed__3;
    v___x_829_ = leanh::lean_alloc_ctor(0, 7, (1) as u32);
    leanh::lean_ctor_set(v___x_829_, 0, v___x_823_);
    leanh::lean_ctor_set(v___x_829_, 1, v___x_824_);
    leanh::lean_ctor_set(v___x_829_, 2, v_name_821_);
    leanh::lean_ctor_set(v___x_829_, 3, v___x_827_);
    leanh::lean_ctor_set(v___x_829_, 4, v___x_828_);
    leanh::lean_ctor_set(v___x_829_, 5, v___x_828_);
    leanh::lean_ctor_set(v___x_829_, 6, v___f_822_);
    leanh::lean_ctor_set_uint8(
        v___x_829_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
        v___x_826_,
    );
    return v___x_829_;
}
pub unsafe fn l_Lake_instInhabitedLeanExeConfig(
    mut v_a_830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_831_ = l_Lake_instInhabitedLeanExeConfig_default(v_a_830_);
    return v___x_831_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir___proj___lam__0(
    mut v_cfg_832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_srcDir_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_srcDir_833_ = leanh::lean_ctor_get(v_cfg_832_, 1);
    leanh::lean_inc_ref(v_srcDir_833_);
    return v_srcDir_833_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir___proj___lam__0___boxed(
    mut v_cfg_834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_835_ = l_Lake_LeanExeConfig_srcDir___proj___lam__0(v_cfg_834_);
    leanh::lean_dec_ref(v_cfg_834_);
    return v_res_835_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir___proj___lam__1(
    mut v_val_836_: *mut leanh::LeanObject,
    mut v_cfg_837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toLeanConfig_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_843_: u8 = 0;
    let mut v_nativeFacets_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_847_: u8 = 0;
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_851_: u8 = 0;
    let mut v_unused_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_838_ = leanh::lean_ctor_get(v_cfg_837_, 0);
                v_root_839_ = leanh::lean_ctor_get(v_cfg_837_, 2);
                v_exeName_840_ = leanh::lean_ctor_get(v_cfg_837_, 3);
                v_needs_841_ = leanh::lean_ctor_get(v_cfg_837_, 4);
                v_extraDepTargets_842_ = leanh::lean_ctor_get(v_cfg_837_, 5);
                v_supportInterpreter_843_ = leanh::lean_ctor_get_uint8(
                    v_cfg_837_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_844_ = leanh::lean_ctor_get(v_cfg_837_, 6);
                v_isSharedCheck_851_ = (!leanh::lean_is_exclusive(v_cfg_837_)) as u8;
                if v_isSharedCheck_851_ == 0 {
                    v_unused_852_ = leanh::lean_ctor_get(v_cfg_837_, 1);
                    leanh::lean_dec(v_unused_852_);
                    v___x_846_ = v_cfg_837_;
                    v_isShared_847_ = v_isSharedCheck_851_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nativeFacets_844_);
                    leanh::lean_inc(v_extraDepTargets_842_);
                    leanh::lean_inc(v_needs_841_);
                    leanh::lean_inc(v_exeName_840_);
                    leanh::lean_inc(v_root_839_);
                    leanh::lean_inc(v_toLeanConfig_838_);
                    leanh::lean_dec(v_cfg_837_);
                    v___x_846_ = leanh::lean_box(0);
                    v_isShared_847_ = v_isSharedCheck_851_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_847_ == 0 {
                    leanh::lean_ctor_set(v___x_846_, 1, v_val_836_);
                    v___x_849_ = v___x_846_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_850_ = leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_850_, 0, v_toLeanConfig_838_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_850_, 1, v_val_836_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_850_, 2, v_root_839_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_850_, 3, v_exeName_840_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_850_, 4, v_needs_841_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_850_, 5, v_extraDepTargets_842_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_850_, 6, v_nativeFacets_844_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_850_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
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
    mut v_f_853_: *mut leanh::LeanObject,
    mut v_cfg_854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toLeanConfig_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_861_: u8 = 0;
    let mut v_nativeFacets_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_865_: u8 = 0;
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_870_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_855_ = leanh::lean_ctor_get(v_cfg_854_, 0);
                v_srcDir_856_ = leanh::lean_ctor_get(v_cfg_854_, 1);
                v_root_857_ = leanh::lean_ctor_get(v_cfg_854_, 2);
                v_exeName_858_ = leanh::lean_ctor_get(v_cfg_854_, 3);
                v_needs_859_ = leanh::lean_ctor_get(v_cfg_854_, 4);
                v_extraDepTargets_860_ = leanh::lean_ctor_get(v_cfg_854_, 5);
                v_supportInterpreter_861_ = leanh::lean_ctor_get_uint8(
                    v_cfg_854_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_862_ = leanh::lean_ctor_get(v_cfg_854_, 6);
                v_isSharedCheck_870_ = (!leanh::lean_is_exclusive(v_cfg_854_)) as u8;
                if v_isSharedCheck_870_ == 0 {
                    v___x_864_ = v_cfg_854_;
                    v_isShared_865_ = v_isSharedCheck_870_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nativeFacets_862_);
                    leanh::lean_inc(v_extraDepTargets_860_);
                    leanh::lean_inc(v_needs_859_);
                    leanh::lean_inc(v_exeName_858_);
                    leanh::lean_inc(v_root_857_);
                    leanh::lean_inc(v_srcDir_856_);
                    leanh::lean_inc(v_toLeanConfig_855_);
                    leanh::lean_dec(v_cfg_854_);
                    v___x_864_ = leanh::lean_box(0);
                    v_isShared_865_ = v_isSharedCheck_870_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_866_ = leanh::lean_apply_1(v_f_853_, v_srcDir_856_);
                if v_isShared_865_ == 0 {
                    leanh::lean_ctor_set(v___x_864_, 1, v___x_866_);
                    v___x_868_ = v___x_864_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_869_ = leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_869_, 0, v_toLeanConfig_855_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_866_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_869_, 2, v_root_857_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_869_, 3, v_exeName_858_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_869_, 4, v_needs_859_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_869_, 5, v_extraDepTargets_860_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_869_, 6, v_nativeFacets_862_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_869_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
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
    mut v_x_871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_872_ = l_Lake_instInhabitedLeanExeConfig_default___closed__1;
    return v___x_872_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir___proj___lam__3___boxed(
    mut v_x_873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_874_ = l_Lake_LeanExeConfig_srcDir___proj___lam__3(v_x_873_);
    leanh::lean_dec_ref(v_x_873_);
    return v_res_874_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir___proj(
    mut v_name_884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_885_ = l_Lake_LeanExeConfig_srcDir___proj___closed__4;
    return v___x_885_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir___proj___boxed(
    mut v_name_886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_887_ = l_Lake_LeanExeConfig_srcDir___proj(v_name_886_);
    leanh::lean_dec(v_name_886_);
    return v_res_887_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir_instConfigField(
    mut v_name_888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_889_ = l_Lake_LeanExeConfig_srcDir___proj(v_name_888_);
    return v___x_889_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir_instConfigField___boxed(
    mut v_name_890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_891_ = l_Lake_LeanExeConfig_srcDir_instConfigField(v_name_890_);
    leanh::lean_dec(v_name_890_);
    return v_res_891_;
}
pub unsafe fn l_Lake_LeanExeConfig_root___proj___lam__0(
    mut v_cfg_892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_root_893_ = leanh::lean_ctor_get(v_cfg_892_, 2);
    leanh::lean_inc(v_root_893_);
    return v_root_893_;
}
pub unsafe fn l_Lake_LeanExeConfig_root___proj___lam__0___boxed(
    mut v_cfg_894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_895_ = l_Lake_LeanExeConfig_root___proj___lam__0(v_cfg_894_);
    leanh::lean_dec_ref(v_cfg_894_);
    return v_res_895_;
}
pub unsafe fn l_Lake_LeanExeConfig_root___proj___lam__1(
    mut v_val_896_: *mut leanh::LeanObject,
    mut v_cfg_897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toLeanConfig_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_903_: u8 = 0;
    let mut v_nativeFacets_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_907_: u8 = 0;
    let mut v___x_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_911_: u8 = 0;
    let mut v_unused_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_898_ = leanh::lean_ctor_get(v_cfg_897_, 0);
                v_srcDir_899_ = leanh::lean_ctor_get(v_cfg_897_, 1);
                v_exeName_900_ = leanh::lean_ctor_get(v_cfg_897_, 3);
                v_needs_901_ = leanh::lean_ctor_get(v_cfg_897_, 4);
                v_extraDepTargets_902_ = leanh::lean_ctor_get(v_cfg_897_, 5);
                v_supportInterpreter_903_ = leanh::lean_ctor_get_uint8(
                    v_cfg_897_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_904_ = leanh::lean_ctor_get(v_cfg_897_, 6);
                v_isSharedCheck_911_ = (!leanh::lean_is_exclusive(v_cfg_897_)) as u8;
                if v_isSharedCheck_911_ == 0 {
                    v_unused_912_ = leanh::lean_ctor_get(v_cfg_897_, 2);
                    leanh::lean_dec(v_unused_912_);
                    v___x_906_ = v_cfg_897_;
                    v_isShared_907_ = v_isSharedCheck_911_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nativeFacets_904_);
                    leanh::lean_inc(v_extraDepTargets_902_);
                    leanh::lean_inc(v_needs_901_);
                    leanh::lean_inc(v_exeName_900_);
                    leanh::lean_inc(v_srcDir_899_);
                    leanh::lean_inc(v_toLeanConfig_898_);
                    leanh::lean_dec(v_cfg_897_);
                    v___x_906_ = leanh::lean_box(0);
                    v_isShared_907_ = v_isSharedCheck_911_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_907_ == 0 {
                    leanh::lean_ctor_set(v___x_906_, 2, v_val_896_);
                    v___x_909_ = v___x_906_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_910_ = leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_910_, 0, v_toLeanConfig_898_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_910_, 1, v_srcDir_899_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_910_, 2, v_val_896_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_910_, 3, v_exeName_900_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_910_, 4, v_needs_901_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_910_, 5, v_extraDepTargets_902_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_910_, 6, v_nativeFacets_904_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_910_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
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
    mut v_f_913_: *mut leanh::LeanObject,
    mut v_cfg_914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toLeanConfig_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_921_: u8 = 0;
    let mut v_nativeFacets_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_925_: u8 = 0;
    let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_915_ = leanh::lean_ctor_get(v_cfg_914_, 0);
                v_srcDir_916_ = leanh::lean_ctor_get(v_cfg_914_, 1);
                v_root_917_ = leanh::lean_ctor_get(v_cfg_914_, 2);
                v_exeName_918_ = leanh::lean_ctor_get(v_cfg_914_, 3);
                v_needs_919_ = leanh::lean_ctor_get(v_cfg_914_, 4);
                v_extraDepTargets_920_ = leanh::lean_ctor_get(v_cfg_914_, 5);
                v_supportInterpreter_921_ = leanh::lean_ctor_get_uint8(
                    v_cfg_914_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_922_ = leanh::lean_ctor_get(v_cfg_914_, 6);
                v_isSharedCheck_930_ = (!leanh::lean_is_exclusive(v_cfg_914_)) as u8;
                if v_isSharedCheck_930_ == 0 {
                    v___x_924_ = v_cfg_914_;
                    v_isShared_925_ = v_isSharedCheck_930_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nativeFacets_922_);
                    leanh::lean_inc(v_extraDepTargets_920_);
                    leanh::lean_inc(v_needs_919_);
                    leanh::lean_inc(v_exeName_918_);
                    leanh::lean_inc(v_root_917_);
                    leanh::lean_inc(v_srcDir_916_);
                    leanh::lean_inc(v_toLeanConfig_915_);
                    leanh::lean_dec(v_cfg_914_);
                    v___x_924_ = leanh::lean_box(0);
                    v_isShared_925_ = v_isSharedCheck_930_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_926_ = leanh::lean_apply_1(v_f_913_, v_root_917_);
                if v_isShared_925_ == 0 {
                    leanh::lean_ctor_set(v___x_924_, 2, v___x_926_);
                    v___x_928_ = v___x_924_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_929_ = leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_929_, 0, v_toLeanConfig_915_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_929_, 1, v_srcDir_916_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_929_, 2, v___x_926_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_929_, 3, v_exeName_918_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_929_, 4, v_needs_919_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_929_, 5, v_extraDepTargets_920_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_929_, 6, v_nativeFacets_922_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_929_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
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
    mut v_name_931_: *mut leanh::LeanObject,
    mut v_x_932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_name_931_);
    return v_name_931_;
}
pub unsafe fn l_Lake_LeanExeConfig_root___proj___lam__3___boxed(
    mut v_name_933_: *mut leanh::LeanObject,
    mut v_x_934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_935_ = l_Lake_LeanExeConfig_root___proj___lam__3(v_name_933_, v_x_934_);
    leanh::lean_dec_ref(v_x_934_);
    leanh::lean_dec(v_name_933_);
    return v_res_935_;
}
pub unsafe fn l_Lake_LeanExeConfig_root___proj(
    mut v_name_939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_940_ = l_Lake_LeanExeConfig_root___proj___closed__0;
    v___f_941_ = l_Lake_LeanExeConfig_root___proj___closed__1;
    v___f_942_ = l_Lake_LeanExeConfig_root___proj___closed__2;
    v___f_943_ = leanh::lean_alloc_closure(
        l_Lake_LeanExeConfig_root___proj___lam__3___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_943_, 0, v_name_939_);
    v___x_944_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_944_, 0, v___f_940_);
    leanh::lean_ctor_set(v___x_944_, 1, v___f_941_);
    leanh::lean_ctor_set(v___x_944_, 2, v___f_942_);
    leanh::lean_ctor_set(v___x_944_, 3, v___f_943_);
    return v___x_944_;
}
pub unsafe fn l_Lake_LeanExeConfig_root_instConfigField(
    mut v_name_945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_946_ = l_Lake_LeanExeConfig_root___proj(v_name_945_);
    return v___x_946_;
}
pub unsafe fn l_Lake_LeanExeConfig_exeName___proj___lam__0(
    mut v_cfg_947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_exeName_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_exeName_948_ = leanh::lean_ctor_get(v_cfg_947_, 3);
    leanh::lean_inc_ref(v_exeName_948_);
    return v_exeName_948_;
}
pub unsafe fn l_Lake_LeanExeConfig_exeName___proj___lam__0___boxed(
    mut v_cfg_949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_950_ = l_Lake_LeanExeConfig_exeName___proj___lam__0(v_cfg_949_);
    leanh::lean_dec_ref(v_cfg_949_);
    return v_res_950_;
}
pub unsafe fn l_Lake_LeanExeConfig_exeName___proj___lam__1(
    mut v_val_951_: *mut leanh::LeanObject,
    mut v_cfg_952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toLeanConfig_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_958_: u8 = 0;
    let mut v_nativeFacets_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_962_: u8 = 0;
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_966_: u8 = 0;
    let mut v_unused_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_953_ = leanh::lean_ctor_get(v_cfg_952_, 0);
                v_srcDir_954_ = leanh::lean_ctor_get(v_cfg_952_, 1);
                v_root_955_ = leanh::lean_ctor_get(v_cfg_952_, 2);
                v_needs_956_ = leanh::lean_ctor_get(v_cfg_952_, 4);
                v_extraDepTargets_957_ = leanh::lean_ctor_get(v_cfg_952_, 5);
                v_supportInterpreter_958_ = leanh::lean_ctor_get_uint8(
                    v_cfg_952_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_959_ = leanh::lean_ctor_get(v_cfg_952_, 6);
                v_isSharedCheck_966_ = (!leanh::lean_is_exclusive(v_cfg_952_)) as u8;
                if v_isSharedCheck_966_ == 0 {
                    v_unused_967_ = leanh::lean_ctor_get(v_cfg_952_, 3);
                    leanh::lean_dec(v_unused_967_);
                    v___x_961_ = v_cfg_952_;
                    v_isShared_962_ = v_isSharedCheck_966_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nativeFacets_959_);
                    leanh::lean_inc(v_extraDepTargets_957_);
                    leanh::lean_inc(v_needs_956_);
                    leanh::lean_inc(v_root_955_);
                    leanh::lean_inc(v_srcDir_954_);
                    leanh::lean_inc(v_toLeanConfig_953_);
                    leanh::lean_dec(v_cfg_952_);
                    v___x_961_ = leanh::lean_box(0);
                    v_isShared_962_ = v_isSharedCheck_966_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_962_ == 0 {
                    leanh::lean_ctor_set(v___x_961_, 3, v_val_951_);
                    v___x_964_ = v___x_961_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_965_ = leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_965_, 0, v_toLeanConfig_953_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_965_, 1, v_srcDir_954_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_965_, 2, v_root_955_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_965_, 3, v_val_951_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_965_, 4, v_needs_956_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_965_, 5, v_extraDepTargets_957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_965_, 6, v_nativeFacets_959_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_965_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
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
    mut v_f_968_: *mut leanh::LeanObject,
    mut v_cfg_969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toLeanConfig_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_976_: u8 = 0;
    let mut v_nativeFacets_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_980_: u8 = 0;
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_985_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_970_ = leanh::lean_ctor_get(v_cfg_969_, 0);
                v_srcDir_971_ = leanh::lean_ctor_get(v_cfg_969_, 1);
                v_root_972_ = leanh::lean_ctor_get(v_cfg_969_, 2);
                v_exeName_973_ = leanh::lean_ctor_get(v_cfg_969_, 3);
                v_needs_974_ = leanh::lean_ctor_get(v_cfg_969_, 4);
                v_extraDepTargets_975_ = leanh::lean_ctor_get(v_cfg_969_, 5);
                v_supportInterpreter_976_ = leanh::lean_ctor_get_uint8(
                    v_cfg_969_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_977_ = leanh::lean_ctor_get(v_cfg_969_, 6);
                v_isSharedCheck_985_ = (!leanh::lean_is_exclusive(v_cfg_969_)) as u8;
                if v_isSharedCheck_985_ == 0 {
                    v___x_979_ = v_cfg_969_;
                    v_isShared_980_ = v_isSharedCheck_985_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nativeFacets_977_);
                    leanh::lean_inc(v_extraDepTargets_975_);
                    leanh::lean_inc(v_needs_974_);
                    leanh::lean_inc(v_exeName_973_);
                    leanh::lean_inc(v_root_972_);
                    leanh::lean_inc(v_srcDir_971_);
                    leanh::lean_inc(v_toLeanConfig_970_);
                    leanh::lean_dec(v_cfg_969_);
                    v___x_979_ = leanh::lean_box(0);
                    v_isShared_980_ = v_isSharedCheck_985_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_981_ = leanh::lean_apply_1(v_f_968_, v_exeName_973_);
                if v_isShared_980_ == 0 {
                    leanh::lean_ctor_set(v___x_979_, 3, v___x_981_);
                    v___x_983_ = v___x_979_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_984_ = leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_984_, 0, v_toLeanConfig_970_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_984_, 1, v_srcDir_971_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_984_, 2, v_root_972_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_984_, 3, v___x_981_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_984_, 4, v_needs_974_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_984_, 5, v_extraDepTargets_975_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_984_, 6, v_nativeFacets_977_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_984_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
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
    mut v_name_986_: *mut leanh::LeanObject,
    mut v_x_987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: u8 = 0;
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_name_991_: *mut leanh::LeanObject,
    mut v_x_992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_993_ = l_Lake_LeanExeConfig_exeName___proj___lam__3(v_name_991_, v_x_992_);
    leanh::lean_dec_ref(v_x_992_);
    return v_res_993_;
}
pub unsafe fn l_Lake_LeanExeConfig_exeName___proj(
    mut v_name_997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_998_ = l_Lake_LeanExeConfig_exeName___proj___closed__0;
    v___f_999_ = l_Lake_LeanExeConfig_exeName___proj___closed__1;
    v___f_1000_ = l_Lake_LeanExeConfig_exeName___proj___closed__2;
    v___f_1001_ = leanh::lean_alloc_closure(
        l_Lake_LeanExeConfig_exeName___proj___lam__3___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1001_, 0, v_name_997_);
    v___x_1002_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1002_, 0, v___f_998_);
    leanh::lean_ctor_set(v___x_1002_, 1, v___f_999_);
    leanh::lean_ctor_set(v___x_1002_, 2, v___f_1000_);
    leanh::lean_ctor_set(v___x_1002_, 3, v___f_1001_);
    return v___x_1002_;
}
pub unsafe fn l_Lake_LeanExeConfig_exeName_instConfigField(
    mut v_name_1003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1004_ = l_Lake_LeanExeConfig_exeName___proj(v_name_1003_);
    return v___x_1004_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs___proj___lam__0(
    mut v_cfg_1005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_needs_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_needs_1006_ = leanh::lean_ctor_get(v_cfg_1005_, 4);
    leanh::lean_inc_ref(v_needs_1006_);
    return v_needs_1006_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs___proj___lam__0___boxed(
    mut v_cfg_1007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1008_ = l_Lake_LeanExeConfig_needs___proj___lam__0(v_cfg_1007_);
    leanh::lean_dec_ref(v_cfg_1007_);
    return v_res_1008_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs___proj___lam__1(
    mut v_val_1009_: *mut leanh::LeanObject,
    mut v_cfg_1010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toLeanConfig_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1016_: u8 = 0;
    let mut v_nativeFacets_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1020_: u8 = 0;
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1024_: u8 = 0;
    let mut v_unused_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1011_ = leanh::lean_ctor_get(v_cfg_1010_, 0);
                v_srcDir_1012_ = leanh::lean_ctor_get(v_cfg_1010_, 1);
                v_root_1013_ = leanh::lean_ctor_get(v_cfg_1010_, 2);
                v_exeName_1014_ = leanh::lean_ctor_get(v_cfg_1010_, 3);
                v_extraDepTargets_1015_ = leanh::lean_ctor_get(v_cfg_1010_, 5);
                v_supportInterpreter_1016_ = leanh::lean_ctor_get_uint8(
                    v_cfg_1010_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1017_ = leanh::lean_ctor_get(v_cfg_1010_, 6);
                v_isSharedCheck_1024_ = (!leanh::lean_is_exclusive(v_cfg_1010_)) as u8;
                if v_isSharedCheck_1024_ == 0 {
                    v_unused_1025_ = leanh::lean_ctor_get(v_cfg_1010_, 4);
                    leanh::lean_dec(v_unused_1025_);
                    v___x_1019_ = v_cfg_1010_;
                    v_isShared_1020_ = v_isSharedCheck_1024_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nativeFacets_1017_);
                    leanh::lean_inc(v_extraDepTargets_1015_);
                    leanh::lean_inc(v_exeName_1014_);
                    leanh::lean_inc(v_root_1013_);
                    leanh::lean_inc(v_srcDir_1012_);
                    leanh::lean_inc(v_toLeanConfig_1011_);
                    leanh::lean_dec(v_cfg_1010_);
                    v___x_1019_ = leanh::lean_box(0);
                    v_isShared_1020_ = v_isSharedCheck_1024_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1020_ == 0 {
                    leanh::lean_ctor_set(v___x_1019_, 4, v_val_1009_);
                    v___x_1022_ = v___x_1019_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1023_ = leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_toLeanConfig_1011_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_srcDir_1012_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1023_, 2, v_root_1013_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1023_, 3, v_exeName_1014_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1023_, 4, v_val_1009_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1023_, 5, v_extraDepTargets_1015_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1023_, 6, v_nativeFacets_1017_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1023_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
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
    mut v_f_1026_: *mut leanh::LeanObject,
    mut v_cfg_1027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toLeanConfig_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1034_: u8 = 0;
    let mut v_nativeFacets_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1038_: u8 = 0;
    let mut v___x_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1028_ = leanh::lean_ctor_get(v_cfg_1027_, 0);
                v_srcDir_1029_ = leanh::lean_ctor_get(v_cfg_1027_, 1);
                v_root_1030_ = leanh::lean_ctor_get(v_cfg_1027_, 2);
                v_exeName_1031_ = leanh::lean_ctor_get(v_cfg_1027_, 3);
                v_needs_1032_ = leanh::lean_ctor_get(v_cfg_1027_, 4);
                v_extraDepTargets_1033_ = leanh::lean_ctor_get(v_cfg_1027_, 5);
                v_supportInterpreter_1034_ = leanh::lean_ctor_get_uint8(
                    v_cfg_1027_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1035_ = leanh::lean_ctor_get(v_cfg_1027_, 6);
                v_isSharedCheck_1043_ = (!leanh::lean_is_exclusive(v_cfg_1027_)) as u8;
                if v_isSharedCheck_1043_ == 0 {
                    v___x_1037_ = v_cfg_1027_;
                    v_isShared_1038_ = v_isSharedCheck_1043_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nativeFacets_1035_);
                    leanh::lean_inc(v_extraDepTargets_1033_);
                    leanh::lean_inc(v_needs_1032_);
                    leanh::lean_inc(v_exeName_1031_);
                    leanh::lean_inc(v_root_1030_);
                    leanh::lean_inc(v_srcDir_1029_);
                    leanh::lean_inc(v_toLeanConfig_1028_);
                    leanh::lean_dec(v_cfg_1027_);
                    v___x_1037_ = leanh::lean_box(0);
                    v_isShared_1038_ = v_isSharedCheck_1043_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1039_ = leanh::lean_apply_1(v_f_1026_, v_needs_1032_);
                if v_isShared_1038_ == 0 {
                    leanh::lean_ctor_set(v___x_1037_, 4, v___x_1039_);
                    v___x_1041_ = v___x_1037_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1042_ = leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_toLeanConfig_1028_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_srcDir_1029_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 2, v_root_1030_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 3, v_exeName_1031_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 4, v___x_1039_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 5, v_extraDepTargets_1033_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 6, v_nativeFacets_1035_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1042_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
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
    mut v_x_1044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1045_ = l_Lake_instInhabitedLeanExeConfig_default___closed__3;
    return v___x_1045_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs___proj___lam__3___boxed(
    mut v_x_1046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1047_ = l_Lake_LeanExeConfig_needs___proj___lam__3(v_x_1046_);
    leanh::lean_dec_ref(v_x_1046_);
    return v_res_1047_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs___proj(
    mut v_name_1057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1058_ = l_Lake_LeanExeConfig_needs___proj___closed__4;
    return v___x_1058_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs___proj___boxed(
    mut v_name_1059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1060_ = l_Lake_LeanExeConfig_needs___proj(v_name_1059_);
    leanh::lean_dec(v_name_1059_);
    return v_res_1060_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs_instConfigField(
    mut v_name_1061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1062_ = l_Lake_LeanExeConfig_needs___proj(v_name_1061_);
    return v___x_1062_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs_instConfigField___boxed(
    mut v_name_1063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1064_ = l_Lake_LeanExeConfig_needs_instConfigField(v_name_1063_);
    leanh::lean_dec(v_name_1063_);
    return v_res_1064_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets___proj___lam__0(
    mut v_cfg_1065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_extraDepTargets_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_extraDepTargets_1066_ = leanh::lean_ctor_get(v_cfg_1065_, 5);
    leanh::lean_inc_ref(v_extraDepTargets_1066_);
    return v_extraDepTargets_1066_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets___proj___lam__0___boxed(
    mut v_cfg_1067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1068_ = l_Lake_LeanExeConfig_extraDepTargets___proj___lam__0(v_cfg_1067_);
    leanh::lean_dec_ref(v_cfg_1067_);
    return v_res_1068_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets___proj___lam__1(
    mut v_val_1069_: *mut leanh::LeanObject,
    mut v_cfg_1070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toLeanConfig_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1076_: u8 = 0;
    let mut v_nativeFacets_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1080_: u8 = 0;
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1084_: u8 = 0;
    let mut v_unused_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1071_ = leanh::lean_ctor_get(v_cfg_1070_, 0);
                v_srcDir_1072_ = leanh::lean_ctor_get(v_cfg_1070_, 1);
                v_root_1073_ = leanh::lean_ctor_get(v_cfg_1070_, 2);
                v_exeName_1074_ = leanh::lean_ctor_get(v_cfg_1070_, 3);
                v_needs_1075_ = leanh::lean_ctor_get(v_cfg_1070_, 4);
                v_supportInterpreter_1076_ = leanh::lean_ctor_get_uint8(
                    v_cfg_1070_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1077_ = leanh::lean_ctor_get(v_cfg_1070_, 6);
                v_isSharedCheck_1084_ = (!leanh::lean_is_exclusive(v_cfg_1070_)) as u8;
                if v_isSharedCheck_1084_ == 0 {
                    v_unused_1085_ = leanh::lean_ctor_get(v_cfg_1070_, 5);
                    leanh::lean_dec(v_unused_1085_);
                    v___x_1079_ = v_cfg_1070_;
                    v_isShared_1080_ = v_isSharedCheck_1084_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nativeFacets_1077_);
                    leanh::lean_inc(v_needs_1075_);
                    leanh::lean_inc(v_exeName_1074_);
                    leanh::lean_inc(v_root_1073_);
                    leanh::lean_inc(v_srcDir_1072_);
                    leanh::lean_inc(v_toLeanConfig_1071_);
                    leanh::lean_dec(v_cfg_1070_);
                    v___x_1079_ = leanh::lean_box(0);
                    v_isShared_1080_ = v_isSharedCheck_1084_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1080_ == 0 {
                    leanh::lean_ctor_set(v___x_1079_, 5, v_val_1069_);
                    v___x_1082_ = v___x_1079_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1083_ = leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_toLeanConfig_1071_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_srcDir_1072_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 2, v_root_1073_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 3, v_exeName_1074_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 4, v_needs_1075_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 5, v_val_1069_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 6, v_nativeFacets_1077_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1083_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
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
    mut v_f_1086_: *mut leanh::LeanObject,
    mut v_cfg_1087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toLeanConfig_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1094_: u8 = 0;
    let mut v_nativeFacets_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1098_: u8 = 0;
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1103_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1088_ = leanh::lean_ctor_get(v_cfg_1087_, 0);
                v_srcDir_1089_ = leanh::lean_ctor_get(v_cfg_1087_, 1);
                v_root_1090_ = leanh::lean_ctor_get(v_cfg_1087_, 2);
                v_exeName_1091_ = leanh::lean_ctor_get(v_cfg_1087_, 3);
                v_needs_1092_ = leanh::lean_ctor_get(v_cfg_1087_, 4);
                v_extraDepTargets_1093_ = leanh::lean_ctor_get(v_cfg_1087_, 5);
                v_supportInterpreter_1094_ = leanh::lean_ctor_get_uint8(
                    v_cfg_1087_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1095_ = leanh::lean_ctor_get(v_cfg_1087_, 6);
                v_isSharedCheck_1103_ = (!leanh::lean_is_exclusive(v_cfg_1087_)) as u8;
                if v_isSharedCheck_1103_ == 0 {
                    v___x_1097_ = v_cfg_1087_;
                    v_isShared_1098_ = v_isSharedCheck_1103_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nativeFacets_1095_);
                    leanh::lean_inc(v_extraDepTargets_1093_);
                    leanh::lean_inc(v_needs_1092_);
                    leanh::lean_inc(v_exeName_1091_);
                    leanh::lean_inc(v_root_1090_);
                    leanh::lean_inc(v_srcDir_1089_);
                    leanh::lean_inc(v_toLeanConfig_1088_);
                    leanh::lean_dec(v_cfg_1087_);
                    v___x_1097_ = leanh::lean_box(0);
                    v_isShared_1098_ = v_isSharedCheck_1103_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1099_ = leanh::lean_apply_1(v_f_1086_, v_extraDepTargets_1093_);
                if v_isShared_1098_ == 0 {
                    leanh::lean_ctor_set(v___x_1097_, 5, v___x_1099_);
                    v___x_1101_ = v___x_1097_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1102_ = leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_toLeanConfig_1088_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_srcDir_1089_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1102_, 2, v_root_1090_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1102_, 3, v_exeName_1091_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1102_, 4, v_needs_1092_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1102_, 5, v___x_1099_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1102_, 6, v_nativeFacets_1095_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1102_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
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
    mut v_x_1106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1107_ = l_Lake_LeanExeConfig_extraDepTargets___proj___lam__3___closed__0;
    return v___x_1107_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets___proj___lam__3___boxed(
    mut v_x_1108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1109_ = l_Lake_LeanExeConfig_extraDepTargets___proj___lam__3(v_x_1108_);
    leanh::lean_dec_ref(v_x_1108_);
    return v_res_1109_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets___proj(
    mut v_name_1119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1120_ = l_Lake_LeanExeConfig_extraDepTargets___proj___closed__4;
    return v___x_1120_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets___proj___boxed(
    mut v_name_1121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1122_ = l_Lake_LeanExeConfig_extraDepTargets___proj(v_name_1121_);
    leanh::lean_dec(v_name_1121_);
    return v_res_1122_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets_instConfigField(
    mut v_name_1123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1124_ = l_Lake_LeanExeConfig_extraDepTargets___proj(v_name_1123_);
    return v___x_1124_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets_instConfigField___boxed(
    mut v_name_1125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1126_ = l_Lake_LeanExeConfig_extraDepTargets_instConfigField(v_name_1125_);
    leanh::lean_dec(v_name_1125_);
    return v_res_1126_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___lam__0(
    mut v_cfg_1127_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_supportInterpreter_1128_: u8 = 0;
    v_supportInterpreter_1128_ = leanh::lean_ctor_get_uint8(
        v_cfg_1127_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
    );
    return v_supportInterpreter_1128_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___lam__0___boxed(
    mut v_cfg_1129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1130_: u8 = 0;
    let mut v_r_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1130_ = l_Lake_LeanExeConfig_supportInterpreter___proj___lam__0(v_cfg_1129_);
    leanh::lean_dec_ref(v_cfg_1129_);
    v_r_1131_ = leanh::lean_box((v_res_1130_) as usize);
    return v_r_1131_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___lam__1(
    mut v_val_1132_: u8,
    mut v_cfg_1133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toLeanConfig_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1143_: u8 = 0;
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1147_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1134_ = leanh::lean_ctor_get(v_cfg_1133_, 0);
                v_srcDir_1135_ = leanh::lean_ctor_get(v_cfg_1133_, 1);
                v_root_1136_ = leanh::lean_ctor_get(v_cfg_1133_, 2);
                v_exeName_1137_ = leanh::lean_ctor_get(v_cfg_1133_, 3);
                v_needs_1138_ = leanh::lean_ctor_get(v_cfg_1133_, 4);
                v_extraDepTargets_1139_ = leanh::lean_ctor_get(v_cfg_1133_, 5);
                v_nativeFacets_1140_ = leanh::lean_ctor_get(v_cfg_1133_, 6);
                v_isSharedCheck_1147_ = (!leanh::lean_is_exclusive(v_cfg_1133_)) as u8;
                if v_isSharedCheck_1147_ == 0 {
                    v___x_1142_ = v_cfg_1133_;
                    v_isShared_1143_ = v_isSharedCheck_1147_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nativeFacets_1140_);
                    leanh::lean_inc(v_extraDepTargets_1139_);
                    leanh::lean_inc(v_needs_1138_);
                    leanh::lean_inc(v_exeName_1137_);
                    leanh::lean_inc(v_root_1136_);
                    leanh::lean_inc(v_srcDir_1135_);
                    leanh::lean_inc(v_toLeanConfig_1134_);
                    leanh::lean_dec(v_cfg_1133_);
                    v___x_1142_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1146_ = leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_toLeanConfig_1134_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_srcDir_1135_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 2, v_root_1136_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 3, v_exeName_1137_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 4, v_needs_1138_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 5, v_extraDepTargets_1139_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 6, v_nativeFacets_1140_);
                    v___x_1145_ = v_reuseFailAlloc_1146_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1145_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_val_1132_,
                );
                return v___x_1145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___lam__1___boxed(
    mut v_val_1148_: *mut leanh::LeanObject,
    mut v_cfg_1149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_59__boxed_1150_: u8 = 0;
    let mut v_res_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_59__boxed_1150_ = (leanh::lean_unbox(v_val_1148_) as u8);
    v_res_1151_ =
        l_Lake_LeanExeConfig_supportInterpreter___proj___lam__1(v_val_59__boxed_1150_, v_cfg_1149_);
    return v_res_1151_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___lam__2(
    mut v_f_1152_: *mut leanh::LeanObject,
    mut v_cfg_1153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toLeanConfig_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1160_: u8 = 0;
    let mut v_nativeFacets_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1164_: u8 = 0;
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: u8 = 0;
    let mut v_reuseFailAlloc_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1171_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1154_ = leanh::lean_ctor_get(v_cfg_1153_, 0);
                v_srcDir_1155_ = leanh::lean_ctor_get(v_cfg_1153_, 1);
                v_root_1156_ = leanh::lean_ctor_get(v_cfg_1153_, 2);
                v_exeName_1157_ = leanh::lean_ctor_get(v_cfg_1153_, 3);
                v_needs_1158_ = leanh::lean_ctor_get(v_cfg_1153_, 4);
                v_extraDepTargets_1159_ = leanh::lean_ctor_get(v_cfg_1153_, 5);
                v_supportInterpreter_1160_ = leanh::lean_ctor_get_uint8(
                    v_cfg_1153_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1161_ = leanh::lean_ctor_get(v_cfg_1153_, 6);
                v_isSharedCheck_1171_ = (!leanh::lean_is_exclusive(v_cfg_1153_)) as u8;
                if v_isSharedCheck_1171_ == 0 {
                    v___x_1163_ = v_cfg_1153_;
                    v_isShared_1164_ = v_isSharedCheck_1171_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nativeFacets_1161_);
                    leanh::lean_inc(v_extraDepTargets_1159_);
                    leanh::lean_inc(v_needs_1158_);
                    leanh::lean_inc(v_exeName_1157_);
                    leanh::lean_inc(v_root_1156_);
                    leanh::lean_inc(v_srcDir_1155_);
                    leanh::lean_inc(v_toLeanConfig_1154_);
                    leanh::lean_dec(v_cfg_1153_);
                    v___x_1163_ = leanh::lean_box(0);
                    v_isShared_1164_ = v_isSharedCheck_1171_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1165_ = leanh::lean_box((v_supportInterpreter_1160_) as usize);
                v___x_1166_ = leanh::lean_apply_1(v_f_1152_, v___x_1165_);
                if v_isShared_1164_ == 0 {
                    v___x_1168_ = v___x_1163_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1170_ = leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_toLeanConfig_1154_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_srcDir_1155_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_root_1156_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1170_, 3, v_exeName_1157_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1170_, 4, v_needs_1158_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1170_, 5, v_extraDepTargets_1159_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1170_, 6, v_nativeFacets_1161_);
                    v___x_1168_ = v_reuseFailAlloc_1170_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1169_ = (leanh::lean_unbox(v___x_1166_) as u8);
                leanh::lean_ctor_set_uint8(
                    v___x_1168_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v___x_1169_,
                );
                return v___x_1168_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___lam__3(
    mut v_x_1172_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1173_: u8 = 0;
    v___x_1173_ = 0;
    return v___x_1173_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___lam__3___boxed(
    mut v_x_1174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1175_: u8 = 0;
    let mut v_r_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1175_ = l_Lake_LeanExeConfig_supportInterpreter___proj___lam__3(v_x_1174_);
    leanh::lean_dec_ref(v_x_1174_);
    v_r_1176_ = leanh::lean_box((v_res_1175_) as usize);
    return v_r_1176_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj(
    mut v_name_1186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1187_ = l_Lake_LeanExeConfig_supportInterpreter___proj___closed__4;
    return v___x_1187_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___boxed(
    mut v_name_1188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1189_ = l_Lake_LeanExeConfig_supportInterpreter___proj(v_name_1188_);
    leanh::lean_dec(v_name_1188_);
    return v_res_1189_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter_instConfigField(
    mut v_name_1190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1191_ = l_Lake_LeanExeConfig_supportInterpreter___proj(v_name_1190_);
    return v___x_1191_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter_instConfigField___boxed(
    mut v_name_1192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1193_ = l_Lake_LeanExeConfig_supportInterpreter_instConfigField(v_name_1192_);
    leanh::lean_dec(v_name_1192_);
    return v_res_1193_;
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets___proj___lam__0(
    mut v_cfg_1194_: *mut leanh::LeanObject,
    mut v___y_1195_: u8,
) -> *mut leanh::LeanObject {
    let mut v_nativeFacets_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nativeFacets_1196_ = leanh::lean_ctor_get(v_cfg_1194_, 6);
    leanh::lean_inc_ref(v_nativeFacets_1196_);
    leanh::lean_dec_ref(v_cfg_1194_);
    v___x_1197_ = leanh::lean_box((v___y_1195_) as usize);
    v___x_1198_ = leanh::lean_apply_1(v_nativeFacets_1196_, v___x_1197_);
    return v___x_1198_;
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets___proj___lam__0___boxed(
    mut v_cfg_1199_: *mut leanh::LeanObject,
    mut v___y_1200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_135__boxed_1201_: u8 = 0;
    let mut v_res_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_135__boxed_1201_ = (leanh::lean_unbox(v___y_1200_) as u8);
    v_res_1202_ =
        l_Lake_LeanExeConfig_nativeFacets___proj___lam__0(v_cfg_1199_, v___y_135__boxed_1201_);
    return v_res_1202_;
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets___proj___lam__1(
    mut v_val_1203_: *mut leanh::LeanObject,
    mut v_cfg_1204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toLeanConfig_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1211_: u8 = 0;
    let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1214_: u8 = 0;
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1218_: u8 = 0;
    let mut v_unused_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1205_ = leanh::lean_ctor_get(v_cfg_1204_, 0);
                v_srcDir_1206_ = leanh::lean_ctor_get(v_cfg_1204_, 1);
                v_root_1207_ = leanh::lean_ctor_get(v_cfg_1204_, 2);
                v_exeName_1208_ = leanh::lean_ctor_get(v_cfg_1204_, 3);
                v_needs_1209_ = leanh::lean_ctor_get(v_cfg_1204_, 4);
                v_extraDepTargets_1210_ = leanh::lean_ctor_get(v_cfg_1204_, 5);
                v_supportInterpreter_1211_ = leanh::lean_ctor_get_uint8(
                    v_cfg_1204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_isSharedCheck_1218_ = (!leanh::lean_is_exclusive(v_cfg_1204_)) as u8;
                if v_isSharedCheck_1218_ == 0 {
                    v_unused_1219_ = leanh::lean_ctor_get(v_cfg_1204_, 6);
                    leanh::lean_dec(v_unused_1219_);
                    v___x_1213_ = v_cfg_1204_;
                    v_isShared_1214_ = v_isSharedCheck_1218_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_extraDepTargets_1210_);
                    leanh::lean_inc(v_needs_1209_);
                    leanh::lean_inc(v_exeName_1208_);
                    leanh::lean_inc(v_root_1207_);
                    leanh::lean_inc(v_srcDir_1206_);
                    leanh::lean_inc(v_toLeanConfig_1205_);
                    leanh::lean_dec(v_cfg_1204_);
                    v___x_1213_ = leanh::lean_box(0);
                    v_isShared_1214_ = v_isSharedCheck_1218_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1214_ == 0 {
                    leanh::lean_ctor_set(v___x_1213_, 6, v_val_1203_);
                    v___x_1216_ = v___x_1213_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1217_ = leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_toLeanConfig_1205_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_srcDir_1206_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1217_, 2, v_root_1207_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1217_, 3, v_exeName_1208_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1217_, 4, v_needs_1209_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1217_, 5, v_extraDepTargets_1210_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1217_, 6, v_val_1203_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1217_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
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
    mut v_f_1220_: *mut leanh::LeanObject,
    mut v_cfg_1221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toLeanConfig_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1228_: u8 = 0;
    let mut v_nativeFacets_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1232_: u8 = 0;
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1222_ = leanh::lean_ctor_get(v_cfg_1221_, 0);
                v_srcDir_1223_ = leanh::lean_ctor_get(v_cfg_1221_, 1);
                v_root_1224_ = leanh::lean_ctor_get(v_cfg_1221_, 2);
                v_exeName_1225_ = leanh::lean_ctor_get(v_cfg_1221_, 3);
                v_needs_1226_ = leanh::lean_ctor_get(v_cfg_1221_, 4);
                v_extraDepTargets_1227_ = leanh::lean_ctor_get(v_cfg_1221_, 5);
                v_supportInterpreter_1228_ = leanh::lean_ctor_get_uint8(
                    v_cfg_1221_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1229_ = leanh::lean_ctor_get(v_cfg_1221_, 6);
                v_isSharedCheck_1237_ = (!leanh::lean_is_exclusive(v_cfg_1221_)) as u8;
                if v_isSharedCheck_1237_ == 0 {
                    v___x_1231_ = v_cfg_1221_;
                    v_isShared_1232_ = v_isSharedCheck_1237_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nativeFacets_1229_);
                    leanh::lean_inc(v_extraDepTargets_1227_);
                    leanh::lean_inc(v_needs_1226_);
                    leanh::lean_inc(v_exeName_1225_);
                    leanh::lean_inc(v_root_1224_);
                    leanh::lean_inc(v_srcDir_1223_);
                    leanh::lean_inc(v_toLeanConfig_1222_);
                    leanh::lean_dec(v_cfg_1221_);
                    v___x_1231_ = leanh::lean_box(0);
                    v_isShared_1232_ = v_isSharedCheck_1237_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1233_ = leanh::lean_apply_1(v_f_1220_, v_nativeFacets_1229_);
                if v_isShared_1232_ == 0 {
                    leanh::lean_ctor_set(v___x_1231_, 6, v___x_1233_);
                    v___x_1235_ = v___x_1231_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1236_ = leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_toLeanConfig_1222_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_srcDir_1223_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 2, v_root_1224_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 3, v_exeName_1225_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 4, v_needs_1226_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 5, v_extraDepTargets_1227_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 6, v___x_1233_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1236_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
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
    mut v_x_1238_: *mut leanh::LeanObject,
    mut v___y_1239_: u8,
) -> *mut leanh::LeanObject {
    let mut v___y_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                v___x_1242_ = leanh::lean_unsigned_to_nat(1);
                v___x_1243_ = lean_mk_empty_array_with_capacity(v___x_1242_);
                leanh::lean_inc(v___y_1241_);
                v___x_1244_ = lean_array_push(v___x_1243_, v___y_1241_);
                return v___x_1244_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets___proj___lam__3___boxed(
    mut v_x_1247_: *mut leanh::LeanObject,
    mut v___y_1248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_185__boxed_1249_: u8 = 0;
    let mut v_res_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_185__boxed_1249_ = (leanh::lean_unbox(v___y_1248_) as u8);
    v_res_1250_ =
        l_Lake_LeanExeConfig_nativeFacets___proj___lam__3(v_x_1247_, v___y_185__boxed_1249_);
    leanh::lean_dec_ref(v_x_1247_);
    return v_res_1250_;
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets___proj(
    mut v_name_1260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1261_ = l_Lake_LeanExeConfig_nativeFacets___proj___closed__4;
    return v___x_1261_;
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets___proj___boxed(
    mut v_name_1262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1263_ = l_Lake_LeanExeConfig_nativeFacets___proj(v_name_1262_);
    leanh::lean_dec(v_name_1262_);
    return v_res_1263_;
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets_instConfigField(
    mut v_name_1264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1265_ = l_Lake_LeanExeConfig_nativeFacets___proj(v_name_1264_);
    return v___x_1265_;
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets_instConfigField___boxed(
    mut v_name_1266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1267_ = l_Lake_LeanExeConfig_nativeFacets_instConfigField(v_name_1266_);
    leanh::lean_dec(v_name_1266_);
    return v_res_1267_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig___proj___lam__0(
    mut v_cfg_1268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toLeanConfig_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toLeanConfig_1269_ = leanh::lean_ctor_get(v_cfg_1268_, 0);
    leanh::lean_inc_ref(v_toLeanConfig_1269_);
    return v_toLeanConfig_1269_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig___proj___lam__0___boxed(
    mut v_cfg_1270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1271_ = l_Lake_LeanExeConfig_toLeanConfig___proj___lam__0(v_cfg_1270_);
    leanh::lean_dec_ref(v_cfg_1270_);
    return v_res_1271_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig___proj___lam__1(
    mut v_val_1272_: *mut leanh::LeanObject,
    mut v_cfg_1273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_srcDir_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1279_: u8 = 0;
    let mut v_nativeFacets_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1283_: u8 = 0;
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1287_: u8 = 0;
    let mut v_unused_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_srcDir_1274_ = leanh::lean_ctor_get(v_cfg_1273_, 1);
                v_root_1275_ = leanh::lean_ctor_get(v_cfg_1273_, 2);
                v_exeName_1276_ = leanh::lean_ctor_get(v_cfg_1273_, 3);
                v_needs_1277_ = leanh::lean_ctor_get(v_cfg_1273_, 4);
                v_extraDepTargets_1278_ = leanh::lean_ctor_get(v_cfg_1273_, 5);
                v_supportInterpreter_1279_ = leanh::lean_ctor_get_uint8(
                    v_cfg_1273_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1280_ = leanh::lean_ctor_get(v_cfg_1273_, 6);
                v_isSharedCheck_1287_ = (!leanh::lean_is_exclusive(v_cfg_1273_)) as u8;
                if v_isSharedCheck_1287_ == 0 {
                    v_unused_1288_ = leanh::lean_ctor_get(v_cfg_1273_, 0);
                    leanh::lean_dec(v_unused_1288_);
                    v___x_1282_ = v_cfg_1273_;
                    v_isShared_1283_ = v_isSharedCheck_1287_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nativeFacets_1280_);
                    leanh::lean_inc(v_extraDepTargets_1278_);
                    leanh::lean_inc(v_needs_1277_);
                    leanh::lean_inc(v_exeName_1276_);
                    leanh::lean_inc(v_root_1275_);
                    leanh::lean_inc(v_srcDir_1274_);
                    leanh::lean_dec(v_cfg_1273_);
                    v___x_1282_ = leanh::lean_box(0);
                    v_isShared_1283_ = v_isSharedCheck_1287_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1283_ == 0 {
                    leanh::lean_ctor_set(v___x_1282_, 0, v_val_1272_);
                    v___x_1285_ = v___x_1282_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1286_ = leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_val_1272_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_srcDir_1274_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 2, v_root_1275_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 3, v_exeName_1276_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 4, v_needs_1277_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 5, v_extraDepTargets_1278_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 6, v_nativeFacets_1280_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1286_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
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
    mut v_f_1289_: *mut leanh::LeanObject,
    mut v_cfg_1290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toLeanConfig_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exeName_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needs_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1297_: u8 = 0;
    let mut v_nativeFacets_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1301_: u8 = 0;
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1306_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1291_ = leanh::lean_ctor_get(v_cfg_1290_, 0);
                v_srcDir_1292_ = leanh::lean_ctor_get(v_cfg_1290_, 1);
                v_root_1293_ = leanh::lean_ctor_get(v_cfg_1290_, 2);
                v_exeName_1294_ = leanh::lean_ctor_get(v_cfg_1290_, 3);
                v_needs_1295_ = leanh::lean_ctor_get(v_cfg_1290_, 4);
                v_extraDepTargets_1296_ = leanh::lean_ctor_get(v_cfg_1290_, 5);
                v_supportInterpreter_1297_ = leanh::lean_ctor_get_uint8(
                    v_cfg_1290_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1298_ = leanh::lean_ctor_get(v_cfg_1290_, 6);
                v_isSharedCheck_1306_ = (!leanh::lean_is_exclusive(v_cfg_1290_)) as u8;
                if v_isSharedCheck_1306_ == 0 {
                    v___x_1300_ = v_cfg_1290_;
                    v_isShared_1301_ = v_isSharedCheck_1306_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nativeFacets_1298_);
                    leanh::lean_inc(v_extraDepTargets_1296_);
                    leanh::lean_inc(v_needs_1295_);
                    leanh::lean_inc(v_exeName_1294_);
                    leanh::lean_inc(v_root_1293_);
                    leanh::lean_inc(v_srcDir_1292_);
                    leanh::lean_inc(v_toLeanConfig_1291_);
                    leanh::lean_dec(v_cfg_1290_);
                    v___x_1300_ = leanh::lean_box(0);
                    v_isShared_1301_ = v_isSharedCheck_1306_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1302_ = leanh::lean_apply_1(v_f_1289_, v_toLeanConfig_1291_);
                if v_isShared_1301_ == 0 {
                    leanh::lean_ctor_set(v___x_1300_, 0, v___x_1302_);
                    v___x_1304_ = v___x_1300_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1305_ = leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_srcDir_1292_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 2, v_root_1293_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 3, v_exeName_1294_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 4, v_needs_1295_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 5, v_extraDepTargets_1296_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 6, v_nativeFacets_1298_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1305_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
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
    mut v_x_1314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1315_ = l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__1;
    return v___x_1315_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___boxed(
    mut v_x_1316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1317_ = l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3(v_x_1316_);
    leanh::lean_dec_ref(v_x_1316_);
    return v_res_1317_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig___proj(
    mut v_name_1327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1328_ = l_Lake_LeanExeConfig_toLeanConfig___proj___closed__4;
    return v___x_1328_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig___proj___boxed(
    mut v_name_1329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1330_ = l_Lake_LeanExeConfig_toLeanConfig___proj(v_name_1329_);
    leanh::lean_dec(v_name_1329_);
    return v_res_1330_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig_instConfigParent(
    mut v_name_1331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1332_ = l_Lake_LeanExeConfig_toLeanConfig___proj(v_name_1331_);
    return v___x_1332_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig_instConfigParent___boxed(
    mut v_name_1333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1334_ = l_Lake_LeanExeConfig_toLeanConfig_instConfigParent(v_name_1333_);
    leanh::lean_dec(v_name_1333_);
    return v_res_1334_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1344_ = l_Lake_LeanExeConfig___fields___closed__3;
    v___x_1345_ = l_Lake_LeanExeConfig___fields___closed__0;
    v___x_1346_ = lean_array_push(v___x_1345_, v___x_1344_);
    return v___x_1346_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1354_ = l_Lake_LeanExeConfig___fields___closed__7;
    v___x_1355_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__4),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__4_once),
        _init_l_Lake_LeanExeConfig___fields___closed__4,
    );
    v___x_1356_ = lean_array_push(v___x_1355_, v___x_1354_);
    return v___x_1356_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1364_ = l_Lake_LeanExeConfig___fields___closed__11;
    v___x_1365_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__8),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__8_once),
        _init_l_Lake_LeanExeConfig___fields___closed__8,
    );
    v___x_1366_ = lean_array_push(v___x_1365_, v___x_1364_);
    return v___x_1366_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__16() -> *mut leanh::LeanObject {
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1374_ = l_Lake_LeanExeConfig___fields___closed__15;
    v___x_1375_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__12),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__12_once),
        _init_l_Lake_LeanExeConfig___fields___closed__12,
    );
    v___x_1376_ = lean_array_push(v___x_1375_, v___x_1374_);
    return v___x_1376_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__20() -> *mut leanh::LeanObject {
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1384_ = l_Lake_LeanExeConfig___fields___closed__19;
    v___x_1385_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__16),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__16_once),
        _init_l_Lake_LeanExeConfig___fields___closed__16,
    );
    v___x_1386_ = lean_array_push(v___x_1385_, v___x_1384_);
    return v___x_1386_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__24() -> *mut leanh::LeanObject {
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1394_ = l_Lake_LeanExeConfig___fields___closed__23;
    v___x_1395_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__20),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__20_once),
        _init_l_Lake_LeanExeConfig___fields___closed__20,
    );
    v___x_1396_ = lean_array_push(v___x_1395_, v___x_1394_);
    return v___x_1396_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__28() -> *mut leanh::LeanObject {
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1404_ = l_Lake_LeanExeConfig___fields___closed__27;
    v___x_1405_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__24),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__24_once),
        _init_l_Lake_LeanExeConfig___fields___closed__24,
    );
    v___x_1406_ = lean_array_push(v___x_1405_, v___x_1404_);
    return v___x_1406_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__29() -> *mut leanh::LeanObject {
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1407_ = l_Lake_LeanConfig___fields;
    v___x_1408_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__28),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__28_once),
        _init_l_Lake_LeanExeConfig___fields___closed__28,
    );
    v___x_1409_ = l_Array_append___redArg(v___x_1408_, v___x_1407_);
    return v___x_1409_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__33() -> *mut leanh::LeanObject {
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1417_ = l_Lake_LeanExeConfig___fields___closed__32;
    v___x_1418_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__29),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__29_once),
        _init_l_Lake_LeanExeConfig___fields___closed__29,
    );
    v___x_1419_ = lean_array_push(v___x_1418_, v___x_1417_);
    return v___x_1419_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields() -> *mut leanh::LeanObject {
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1420_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__33),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__33_once),
        _init_l_Lake_LeanExeConfig___fields___closed__33,
    );
    return v___x_1420_;
}
pub unsafe fn l_Lake_LeanExeConfig_instConfigFields(
    mut v_name_1421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1422_ = l_Lake_LeanExeConfig___fields;
    return v___x_1422_;
}
pub unsafe fn l_Lake_LeanExeConfig_instConfigFields___boxed(
    mut v_name_1423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1424_ = l_Lake_LeanExeConfig_instConfigFields(v_name_1423_);
    leanh::lean_dec(v_name_1423_);
    return v_res_1424_;
}
pub unsafe fn l_Lake_LeanExeConfig_instConfigInfo___lam__0(
    mut v_x1_1425_: *mut leanh::LeanObject,
    mut v_x2_1426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1427_ = leanh::lean_ctor_get(v_x2_1426_, 0);
    leanh::lean_inc(v_name_1427_);
    v___x_1428_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_name_1427_,
        v_x2_1426_,
        v_x1_1425_,
    );
    return v___x_1428_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig_instConfigInfo___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1429_ = l_Lake_LeanExeConfig___fields;
    v___x_1430_ = lean_array_get_size(v___x_1429_);
    return v___x_1430_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig_instConfigInfo___closed__11() -> u8 {
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: u8 = 0;
    v___x_1450_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_LeanExeConfig_instConfigInfo___closed__0,
    );
    v___x_1451_ = leanh::lean_unsigned_to_nat(0);
    v___x_1452_ = lean_nat_dec_lt(v___x_1451_, v___x_1450_);
    return v___x_1452_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig_instConfigInfo___closed__13() -> u8 {
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: u8 = 0;
    v___x_1454_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_LeanExeConfig_instConfigInfo___closed__0,
    );
    v___x_1455_ = lean_nat_dec_le(v___x_1454_, v___x_1454_);
    return v___x_1455_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig_instConfigInfo___closed__14() -> usize {
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: usize = 0;
    v___x_1456_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_LeanExeConfig_instConfigInfo___closed__0,
    );
    v___x_1457_ = lean_usize_of_nat(v___x_1456_);
    return v___x_1457_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig_instConfigInfo___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: usize = 0;
    let mut v___x_1460_: usize = 0;
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1458_ = leanh::lean_box(1);
    v___x_1459_ = leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__14),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__14_once),
        _init_l_Lake_LeanExeConfig_instConfigInfo___closed__14,
    );
    v___x_1460_ = 0usize;
    v___x_1461_ = l_Lake_LeanExeConfig___fields;
    v___f_1462_ = l_Lake_LeanExeConfig_instConfigInfo___closed__12;
    v___x_1463_ = l_Lake_LeanExeConfig_instConfigInfo___closed__10;
    v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1463_,
        v___f_1462_,
        v___x_1461_,
        v___x_1460_,
        v___x_1459_,
        v___x_1458_,
    );
    return v___x_1464_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig_instConfigInfo() -> *mut leanh::LeanObject {
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: u8 = 0;
    let mut v___x_1472_: u8 = 0;
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1465_ = l_Lake_LeanExeConfig___fields;
                v___x_1470_ = leanh::lean_box(1);
                v___x_1471_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__11),
                    core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__11_once),
                    _init_l_Lake_LeanExeConfig_instConfigInfo___closed__11,
                );
                if v___x_1471_ == 0 {
                    v___y_1467_ = v___x_1470_;
                    state = 1;
                    continue;
                } else {
                    v___x_1472_ = leanh::lean_uint8_once(
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
                            v___x_1473_ = leanh::lean_obj_once(
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
                        v___x_1474_ = leanh::lean_obj_once(
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
                v___x_1468_ = leanh::lean_unsigned_to_nat(1);
                leanh::lean_inc(v___y_1467_);
                v___x_1469_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1469_, 0, v___x_1465_);
                leanh::lean_ctor_set(v___x_1469_, 1, v___y_1467_);
                leanh::lean_ctor_set(v___x_1469_, 2, v___x_1468_);
                return v___x_1469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_instEmptyCollection___lam__1(
    mut v___x_1475_: u8,
    mut v_x_1476_: *mut leanh::LeanObject,
) -> u8 {
    return v___x_1475_;
}
pub unsafe fn l_Lake_LeanExeConfig_instEmptyCollection___lam__1___boxed(
    mut v___x_1477_: *mut leanh::LeanObject,
    mut v_x_1478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_83__boxed_1479_: u8 = 0;
    let mut v_res_1480_: u8 = 0;
    let mut v_r_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_83__boxed_1479_ = (leanh::lean_unbox(v___x_1477_) as u8);
    v_res_1480_ =
        l_Lake_LeanExeConfig_instEmptyCollection___lam__1(v___x_83__boxed_1479_, v_x_1478_);
    leanh::lean_dec_ref(v_x_1478_);
    v_r_1481_ = leanh::lean_box((v_res_1480_) as usize);
    return v_r_1481_;
}
pub unsafe fn l_Lake_LeanExeConfig_instEmptyCollection(
    mut v_name_1485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: u8 = 0;
    let mut v___f_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1486_ = l_Lake_instInhabitedLeanExeConfig_default___closed__0;
    v___x_1487_ = l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0;
    v___x_1488_ = l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__1;
    v___x_1489_ = l_Lake_instInhabitedLeanExeConfig_default___closed__1;
    v___x_1490_ = l_Lake_instInhabitedLeanExeConfig_default___closed__2;
    v___x_1491_ = 0;
    v___f_1492_ = l_Lake_LeanExeConfig_instEmptyCollection___closed__0;
    leanh::lean_inc(v_name_1485_);
    v___x_1493_ = l_Lean_Name_toStringWithSep(v___x_1490_, v___x_1491_, v_name_1485_, v___f_1492_);
    v___x_1494_ = leanh::lean_alloc_ctor(0, 7, (1) as u32);
    leanh::lean_ctor_set(v___x_1494_, 0, v___x_1488_);
    leanh::lean_ctor_set(v___x_1494_, 1, v___x_1489_);
    leanh::lean_ctor_set(v___x_1494_, 2, v_name_1485_);
    leanh::lean_ctor_set(v___x_1494_, 3, v___x_1493_);
    leanh::lean_ctor_set(v___x_1494_, 4, v___x_1487_);
    leanh::lean_ctor_set(v___x_1494_, 5, v___x_1487_);
    leanh::lean_ctor_set(v___x_1494_, 6, v___f_1486_);
    leanh::lean_ctor_set_uint8(
        v___x_1494_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
        v___x_1491_,
    );
    return v___x_1494_;
}
pub unsafe fn l_Lake_LeanExeConfig_name___redArg(
    mut v_n_1495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_n_1495_);
    return v_n_1495_;
}
pub unsafe fn l_Lake_LeanExeConfig_name___redArg___boxed(
    mut v_n_1496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1497_ = l_Lake_LeanExeConfig_name___redArg(v_n_1496_);
    leanh::lean_dec(v_n_1496_);
    return v_res_1497_;
}
pub unsafe fn l_Lake_LeanExeConfig_name(
    mut v_n_1498_: *mut leanh::LeanObject,
    mut v_x_1499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_n_1498_);
    return v_n_1498_;
}
pub unsafe fn l_Lake_LeanExeConfig_name___boxed(
    mut v_n_1500_: *mut leanh::LeanObject,
    mut v_x_1501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1502_ = l_Lake_LeanExeConfig_name(v_n_1500_, v_x_1501_);
    leanh::lean_dec_ref(v_x_1501_);
    leanh::lean_dec(v_n_1500_);
    return v_res_1502_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_LeanExeConfig(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Facets(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanConfig(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Meta(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lake_LeanExeConfig___fields = _init_l_Lake_LeanExeConfig___fields();
    leanh::lean_mark_persistent(l_Lake_LeanExeConfig___fields);
    l_Lake_LeanExeConfig_instConfigInfo = _init_l_Lake_LeanExeConfig_instConfigInfo();
    leanh::lean_mark_persistent(l_Lake_LeanExeConfig_instConfigInfo);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_LeanExeConfig(
    builtin: u8,
) -> *mut leanh::LeanObject {
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
pub unsafe fn initialize_Lake_Config_LeanExeConfig(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Facets(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_LeanConfig(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Meta(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Meta(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanExeConfig(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_LeanExeConfig(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Config_LeanExeConfig(builtin);
}