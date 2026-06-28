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
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Lake::Build::Facets::{
    initialize_Lake_Build_Facets, l_Lake_Module_oExportFacet, l_Lake_Module_oFacet,
    runtime_initialize_Lake_Build_Facets,
};
use crate::r#gen::Lake::Config::LeanConfig::{
    initialize_Lake_Config_LeanConfig, l_Lake_LeanConfig___fields,
    l_Lake_instInhabitedLeanConfig_default, runtime_initialize_Lake_Config_LeanConfig,
};
use crate::r#gen::Lake::Config::Meta::{
    initialize_Lake_Config_Meta, meta_initialize_Lake_Config_Meta,
    runtime_initialize_Lake_Config_Meta,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_usize_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
    lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_uint8_once, lean_unbox, lean_unsigned_to_nat, lean_usize_once,
};
pub static l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [91, 97, 110, 111, 110, 121, 109, 111, 117, 115, 93, 0]};
static mut l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lake_instInhabitedLeanExeConfig_default___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instInhabitedLeanExeConfig_default___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instInhabitedLeanExeConfig_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanExeConfig_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedLeanExeConfig_default___closed__1_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instInhabitedLeanExeConfig_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanExeConfig_default___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedLeanExeConfig_default___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instInhabitedLeanExeConfig_default___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanExeConfig_default___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedLeanExeConfig_default___closed__3_value: LeanArrayObject<0> =
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
static mut l_Lake_instInhabitedLeanExeConfig_default___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanExeConfig_default___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_srcDir___proj___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_srcDir___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_srcDir___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_srcDir___proj___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_srcDir___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_srcDir___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_srcDir___proj___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_srcDir___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_srcDir___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_srcDir___proj___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_srcDir___proj___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_srcDir___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__3_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_srcDir___proj___closed__4_value: LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig_srcDir___proj___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_srcDir___proj___closed__4_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_root___proj___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_root___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_root___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_root___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_root___proj___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_root___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_root___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_root___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_root___proj___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_root___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_root___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_root___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_exeName___proj___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_exeName___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_exeName___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_exeName___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_exeName___proj___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_exeName___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_exeName___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_exeName___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_exeName___proj___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_exeName___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_exeName___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_exeName___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_needs___proj___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_needs___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_needs___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_needs___proj___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_needs___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_needs___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_needs___proj___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_needs___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_needs___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_needs___proj___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_needs___proj___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_needs___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__3_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_needs___proj___closed__4_value: LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig_needs___proj___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_needs___proj___closed__4_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_extraDepTargets___proj___lam__3___closed__0_value: LeanArrayObject<
    0,
> = LeanArrayObject {
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
static mut l_Lake_LeanExeConfig_extraDepTargets___proj___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___lam__3___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_extraDepTargets___proj___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_extraDepTargets___proj___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_extraDepTargets___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_extraDepTargets___proj___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_extraDepTargets___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_extraDepTargets___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_extraDepTargets___proj___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_extraDepTargets___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_extraDepTargets___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_extraDepTargets___proj___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_extraDepTargets___proj___lam__3___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_extraDepTargets___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_extraDepTargets___proj___closed__4_value: LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig_extraDepTargets___proj___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_extraDepTargets___proj___closed__4_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_supportInterpreter___proj___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_supportInterpreter___proj___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_supportInterpreter___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_supportInterpreter___proj___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_supportInterpreter___proj___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_supportInterpreter___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_supportInterpreter___proj___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_supportInterpreter___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_supportInterpreter___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_supportInterpreter___proj___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_supportInterpreter___proj___lam__3___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_supportInterpreter___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_supportInterpreter___proj___closed__4_value: LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig_supportInterpreter___proj___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_supportInterpreter___proj___closed__4_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_nativeFacets___proj___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_nativeFacets___proj___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_nativeFacets___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_nativeFacets___proj___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_nativeFacets___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_nativeFacets___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_nativeFacets___proj___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_nativeFacets___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_nativeFacets___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_nativeFacets___proj___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_nativeFacets___proj___lam__3___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_nativeFacets___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_nativeFacets___proj___closed__4_value: LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig_nativeFacets___proj___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_nativeFacets___proj___closed__4_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__1_value: LeanCtorObject<14> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0_value)
                as *mut LeanObject,
            515 as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_toLeanConfig___proj___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_toLeanConfig___proj___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_toLeanConfig___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_toLeanConfig___proj___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_toLeanConfig___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_toLeanConfig___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_toLeanConfig___proj___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_toLeanConfig___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_toLeanConfig___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_toLeanConfig___proj___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_toLeanConfig___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig_toLeanConfig___proj___closed__4_value: LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig_toLeanConfig___proj___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_toLeanConfig___proj___closed__4_value)
        as *mut LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lake_LeanExeConfig___fields___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_LeanExeConfig___fields___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__1_value) as *mut LeanObject,
        10458569134091399506 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig___fields___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__2_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__2_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig___fields___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__3_value) as *mut LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanExeConfig___fields___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanExeConfig___fields___closed__5_value: LeanStringObject<5> =
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
        m_data: [114, 111, 111, 116, 0],
    };
static mut l_Lake_LeanExeConfig___fields___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__5_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__5_value) as *mut LeanObject,
        13952697477363952342 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig___fields___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__6_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__6_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig___fields___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__7_value) as *mut LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanExeConfig___fields___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanExeConfig___fields___closed__9_value: LeanStringObject<8> =
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
        m_data: [101, 120, 101, 78, 97, 109, 101, 0],
    };
static mut l_Lake_LeanExeConfig___fields___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__9_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__9_value) as *mut LeanObject,
        535955292391232655 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig___fields___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__10_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__10_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig___fields___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__11_value) as *mut LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanExeConfig___fields___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanExeConfig___fields___closed__13_value: LeanStringObject<6> =
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
        m_data: [110, 101, 101, 100, 115, 0],
    };
static mut l_Lake_LeanExeConfig___fields___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__13_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__14_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__13_value) as *mut LeanObject,
        14359248566632897495 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig___fields___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__14_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__15_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__14_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__14_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig___fields___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__15_value) as *mut LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanExeConfig___fields___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanExeConfig___fields___closed__17_value: LeanStringObject<16> =
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
            101, 120, 116, 114, 97, 68, 101, 112, 84, 97, 114, 103, 101, 116, 115, 0,
        ],
    };
static mut l_Lake_LeanExeConfig___fields___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__17_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__18_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__17_value) as *mut LeanObject,
        376106234249747944 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig___fields___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__18_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__19_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__18_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__18_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig___fields___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__19_value) as *mut LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanExeConfig___fields___closed__20: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanExeConfig___fields___closed__21_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_LeanExeConfig___fields___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__21_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__22_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__21_value) as *mut LeanObject,
        3358201691291746559 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig___fields___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__22_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__23_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__22_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__22_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig___fields___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__23_value) as *mut LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanExeConfig___fields___closed__24: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanExeConfig___fields___closed__25_value: LeanStringObject<13> =
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
        m_data: [110, 97, 116, 105, 118, 101, 70, 97, 99, 101, 116, 115, 0],
    };
static mut l_Lake_LeanExeConfig___fields___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__25_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__26_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__25_value) as *mut LeanObject,
        2134236907718250370 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig___fields___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__26_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__27_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__26_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__26_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig___fields___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__27_value) as *mut LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__28_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanExeConfig___fields___closed__28: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_LeanExeConfig___fields___closed__29_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanExeConfig___fields___closed__29: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanExeConfig___fields___closed__30_value: LeanStringObject<13> =
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
        m_data: [116, 111, 76, 101, 97, 110, 67, 111, 110, 102, 105, 103, 0],
    };
static mut l_Lake_LeanExeConfig___fields___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__30_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__31_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__30_value) as *mut LeanObject,
        782171420137495241 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig___fields___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__31_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig___fields___closed__32_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__31_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__31_value) as *mut LeanObject,
        256 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanExeConfig___fields___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig___fields___closed__32_value) as *mut LeanObject;
static mut l_Lake_LeanExeConfig___fields___closed__33_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanExeConfig___fields___closed__33: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_LeanExeConfig___fields: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__1_value: LeanClosureObject<0> =
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
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__2_value: LeanClosureObject<0> =
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
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__2_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__3_value: LeanClosureObject<0> =
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
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__3_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__4_value: LeanClosureObject<0> =
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
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__4_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__5_value: LeanClosureObject<0> =
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
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__5_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__6_value: LeanClosureObject<0> =
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
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__6_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__7_value: LeanClosureObject<0> =
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
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__7_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__8_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__8_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__9_value: LeanCtorObject<5> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__9_value) as *mut LeanObject;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__10_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__10_value) as *mut LeanObject;
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__11: u8 = 0;
pub static l_Lake_LeanExeConfig_instConfigInfo___closed__12_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanExeConfig_instConfigInfo___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instConfigInfo___closed__12_value) as *mut LeanObject;
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__13: u8 = 0;
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__14: usize = 0;
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanExeConfig_instConfigInfo___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_LeanExeConfig_instConfigInfo: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanExeConfig_instEmptyCollection___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanExeConfig_instEmptyCollection___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lake_LeanExeConfig_instEmptyCollection___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanExeConfig_instEmptyCollection___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Lake_instInhabitedLeanExeConfig_default___lam__0(
    mut v_shouldExport_752_: u8,
) -> *mut LeanObject {
    let mut v___y_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
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
                v___x_755_ = lean_unsigned_to_nat(1);
                v___x_756_ = lean_mk_empty_array_with_capacity(v___x_755_);
                lean_inc(v___y_754_);
                v___x_757_ = lean_array_push(v___x_756_, v___y_754_);
                return v___x_757_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instInhabitedLeanExeConfig_default___lam__0___boxed(
    mut v_shouldExport_760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_shouldExport_boxed_761_: u8 = 0;
    let mut v_res_762_: *mut LeanObject = core::ptr::null_mut();
    v_shouldExport_boxed_761_ = (lean_unbox(v_shouldExport_760_) as u8);
    v_res_762_ = l_Lake_instInhabitedLeanExeConfig_default___lam__0(v_shouldExport_boxed_761_);
    return v_res_762_;
}
pub unsafe fn l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0(
    mut v_sep_764_: *mut LeanObject,
    mut v_escape_765_: u8,
    mut v_n_766_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_n_766_) {
        0 => {
            let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
            v___x_767_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0___closed__0;
            return v___x_767_;
        }
        1 => {
            let mut v_pre_768_: *mut LeanObject = core::ptr::null_mut();
            v_pre_768_ = lean_ctor_get(v_n_766_, 0);
            if lean_obj_tag(v_pre_768_) == 0 {
                let mut v_str_769_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_770_: u8 = 0;
                let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
                v_str_769_ = lean_ctor_get(v_n_766_, 1);
                lean_inc_ref(v_str_769_);
                lean_dec_ref_known(v_n_766_, 2);
                v___x_770_ = 0;
                v___x_771_ =
                    l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(
                        v_escape_765_,
                        v_str_769_,
                        v___x_770_,
                    );
                return v___x_771_;
            } else {
                let mut v_str_772_: *mut LeanObject = core::ptr::null_mut();
                let mut v_r_773_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_775_: u8 = 0;
                let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
                let mut v_r_x27_777_: *mut LeanObject = core::ptr::null_mut();
                lean_inc(v_pre_768_);
                v_str_772_ = lean_ctor_get(v_n_766_, 1);
                lean_inc_ref(v_str_772_);
                lean_dec_ref_known(v_n_766_, 2);
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
                lean_dec_ref(v___x_776_);
                return v_r_x27_777_;
            }
        }
        _ => {
            let mut v_pre_778_: *mut LeanObject = core::ptr::null_mut();
            v_pre_778_ = lean_ctor_get(v_n_766_, 0);
            if lean_obj_tag(v_pre_778_) == 0 {
                let mut v_i_779_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
                v_i_779_ = lean_ctor_get(v_n_766_, 1);
                lean_inc(v_i_779_);
                lean_dec_ref_known(v_n_766_, 2);
                v___x_780_ = l_Nat_reprFast(v_i_779_);
                return v___x_780_;
            } else {
                let mut v_i_781_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
                lean_inc(v_pre_778_);
                v_i_781_ = lean_ctor_get(v_n_766_, 1);
                lean_inc(v_i_781_);
                lean_dec_ref_known(v_n_766_, 2);
                v___x_782_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0(v_sep_764_, v_escape_765_, v_pre_778_);
                v___x_783_ = lean_string_append(v___x_782_, v_sep_764_);
                v___x_784_ = l_Nat_reprFast(v_i_781_);
                v___x_785_ = lean_string_append(v___x_783_, v___x_784_);
                lean_dec_ref(v___x_784_);
                return v___x_785_;
            }
        }
    }
}
pub unsafe fn l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0___boxed(
    mut v_sep_786_: *mut LeanObject,
    mut v_escape_787_: *mut LeanObject,
    mut v_n_788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_escape_boxed_789_: u8 = 0;
    let mut v_res_790_: *mut LeanObject = core::ptr::null_mut();
    v_escape_boxed_789_ = (lean_unbox(v_escape_787_) as u8);
    v_res_790_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0(v_sep_786_, v_escape_boxed_789_, v_n_788_);
    lean_dec_ref(v_sep_786_);
    return v_res_790_;
}
pub unsafe fn l_Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0(
    mut v_sep_791_: *mut LeanObject,
    mut v_escape_792_: u8,
    mut v_n_793_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_n_793_) {
        0 => {
            let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
            v___x_794_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0___closed__0;
            return v___x_794_;
        }
        1 => {
            let mut v_pre_795_: *mut LeanObject = core::ptr::null_mut();
            let mut v_str_796_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_797_: u8 = 0;
            v_pre_795_ = lean_ctor_get(v_n_793_, 0);
            lean_inc(v_pre_795_);
            v_str_796_ = lean_ctor_get(v_n_793_, 1);
            lean_inc_ref(v_str_796_);
            lean_dec_ref_known(v_n_793_, 2);
            v___x_797_ = 0;
            if lean_obj_tag(v_pre_795_) == 0 {
                let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
                v___x_798_ =
                    l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(
                        v_escape_792_,
                        v_str_796_,
                        v___x_797_,
                    );
                return v___x_798_;
            } else {
                let mut v_r_799_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
                let mut v_r_x27_802_: *mut LeanObject = core::ptr::null_mut();
                v_r_799_ = l_Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0(v_sep_791_, v_escape_792_, v_pre_795_);
                v___x_800_ = lean_string_append(v_r_799_, v_sep_791_);
                v___x_801_ =
                    l___private_Init_Data_ToString_Name_0__Lean_Name_toStringWithSep_maybeEscape(
                        v_escape_792_,
                        v_str_796_,
                        v___x_797_,
                    );
                v_r_x27_802_ = lean_string_append(v___x_800_, v___x_801_);
                lean_dec_ref(v___x_801_);
                return v_r_x27_802_;
            }
        }
        _ => {
            let mut v_pre_803_: *mut LeanObject = core::ptr::null_mut();
            v_pre_803_ = lean_ctor_get(v_n_793_, 0);
            if lean_obj_tag(v_pre_803_) == 0 {
                let mut v_i_804_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
                v_i_804_ = lean_ctor_get(v_n_793_, 1);
                lean_inc(v_i_804_);
                lean_dec_ref_known(v_n_793_, 2);
                v___x_805_ = l_Nat_reprFast(v_i_804_);
                return v___x_805_;
            } else {
                let mut v_i_806_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
                lean_inc(v_pre_803_);
                v_i_806_ = lean_ctor_get(v_n_793_, 1);
                lean_inc(v_i_806_);
                lean_dec_ref_known(v_n_793_, 2);
                v___x_807_ = l_Lean_Name_toStringWithSep___at___00Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0_spec__0(v_sep_791_, v_escape_792_, v_pre_803_);
                v___x_808_ = lean_string_append(v___x_807_, v_sep_791_);
                v___x_809_ = l_Nat_reprFast(v_i_806_);
                v___x_810_ = lean_string_append(v___x_808_, v___x_809_);
                lean_dec_ref(v___x_809_);
                return v___x_810_;
            }
        }
    }
}
pub unsafe fn l_Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0___boxed(
    mut v_sep_811_: *mut LeanObject,
    mut v_escape_812_: *mut LeanObject,
    mut v_n_813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_escape_boxed_814_: u8 = 0;
    let mut v_res_815_: *mut LeanObject = core::ptr::null_mut();
    v_escape_boxed_814_ = (lean_unbox(v_escape_812_) as u8);
    v_res_815_ =
        l_Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0(
            v_sep_811_,
            v_escape_boxed_814_,
            v_n_813_,
        );
    lean_dec_ref(v_sep_811_);
    return v_res_815_;
}
pub unsafe fn l_Lake_instInhabitedLeanExeConfig_default(
    mut v_name_821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: u8 = 0;
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    v___f_822_ = l_Lake_instInhabitedLeanExeConfig_default___closed__0;
    v___x_823_ = l_Lake_instInhabitedLeanConfig_default;
    v___x_824_ = l_Lake_instInhabitedLeanExeConfig_default___closed__1;
    v___x_825_ = l_Lake_instInhabitedLeanExeConfig_default___closed__2;
    v___x_826_ = 0;
    lean_inc(v_name_821_);
    v___x_827_ =
        l_Lean_Name_toStringWithSep___at___00Lake_instInhabitedLeanExeConfig_default_spec__0(
            v___x_825_,
            v___x_826_,
            v_name_821_,
        );
    v___x_828_ = l_Lake_instInhabitedLeanExeConfig_default___closed__3;
    v___x_829_ = lean_alloc_ctor(0, 7, (1) as u32);
    lean_ctor_set(v___x_829_, 0, v___x_823_);
    lean_ctor_set(v___x_829_, 1, v___x_824_);
    lean_ctor_set(v___x_829_, 2, v_name_821_);
    lean_ctor_set(v___x_829_, 3, v___x_827_);
    lean_ctor_set(v___x_829_, 4, v___x_828_);
    lean_ctor_set(v___x_829_, 5, v___x_828_);
    lean_ctor_set(v___x_829_, 6, v___f_822_);
    lean_ctor_set_uint8(
        v___x_829_,
        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
        v___x_826_,
    );
    return v___x_829_;
}
pub unsafe fn l_Lake_instInhabitedLeanExeConfig(mut v_a_830_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    v___x_831_ = l_Lake_instInhabitedLeanExeConfig_default(v_a_830_);
    return v___x_831_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir___proj___lam__0(
    mut v_cfg_832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_srcDir_833_: *mut LeanObject = core::ptr::null_mut();
    v_srcDir_833_ = lean_ctor_get(v_cfg_832_, 1);
    lean_inc_ref(v_srcDir_833_);
    return v_srcDir_833_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir___proj___lam__0___boxed(
    mut v_cfg_834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_835_: *mut LeanObject = core::ptr::null_mut();
    v_res_835_ = l_Lake_LeanExeConfig_srcDir___proj___lam__0(v_cfg_834_);
    lean_dec_ref(v_cfg_834_);
    return v_res_835_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir___proj___lam__1(
    mut v_val_836_: *mut LeanObject,
    mut v_cfg_837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toLeanConfig_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exeName_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_needs_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_843_: u8 = 0;
    let mut v_nativeFacets_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_847_: u8 = 0;
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_851_: u8 = 0;
    let mut v_unused_852_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_838_ = lean_ctor_get(v_cfg_837_, 0);
                v_root_839_ = lean_ctor_get(v_cfg_837_, 2);
                v_exeName_840_ = lean_ctor_get(v_cfg_837_, 3);
                v_needs_841_ = lean_ctor_get(v_cfg_837_, 4);
                v_extraDepTargets_842_ = lean_ctor_get(v_cfg_837_, 5);
                v_supportInterpreter_843_ = lean_ctor_get_uint8(
                    v_cfg_837_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_nativeFacets_844_ = lean_ctor_get(v_cfg_837_, 6);
                v_isSharedCheck_851_ = (!lean_is_exclusive(v_cfg_837_)) as u8;
                if v_isSharedCheck_851_ == 0 {
                    v_unused_852_ = lean_ctor_get(v_cfg_837_, 1);
                    lean_dec(v_unused_852_);
                    v___x_846_ = v_cfg_837_;
                    v_isShared_847_ = v_isSharedCheck_851_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nativeFacets_844_);
                    lean_inc(v_extraDepTargets_842_);
                    lean_inc(v_needs_841_);
                    lean_inc(v_exeName_840_);
                    lean_inc(v_root_839_);
                    lean_inc(v_toLeanConfig_838_);
                    lean_dec(v_cfg_837_);
                    v___x_846_ = lean_box(0);
                    v_isShared_847_ = v_isSharedCheck_851_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_847_ == 0 {
                    lean_ctor_set(v___x_846_, 1, v_val_836_);
                    v___x_849_ = v___x_846_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_850_, 0, v_toLeanConfig_838_);
                    lean_ctor_set(v_reuseFailAlloc_850_, 1, v_val_836_);
                    lean_ctor_set(v_reuseFailAlloc_850_, 2, v_root_839_);
                    lean_ctor_set(v_reuseFailAlloc_850_, 3, v_exeName_840_);
                    lean_ctor_set(v_reuseFailAlloc_850_, 4, v_needs_841_);
                    lean_ctor_set(v_reuseFailAlloc_850_, 5, v_extraDepTargets_842_);
                    lean_ctor_set(v_reuseFailAlloc_850_, 6, v_nativeFacets_844_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_850_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
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
    mut v_f_853_: *mut LeanObject,
    mut v_cfg_854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toLeanConfig_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exeName_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_needs_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_861_: u8 = 0;
    let mut v_nativeFacets_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_865_: u8 = 0;
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_870_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_855_ = lean_ctor_get(v_cfg_854_, 0);
                v_srcDir_856_ = lean_ctor_get(v_cfg_854_, 1);
                v_root_857_ = lean_ctor_get(v_cfg_854_, 2);
                v_exeName_858_ = lean_ctor_get(v_cfg_854_, 3);
                v_needs_859_ = lean_ctor_get(v_cfg_854_, 4);
                v_extraDepTargets_860_ = lean_ctor_get(v_cfg_854_, 5);
                v_supportInterpreter_861_ = lean_ctor_get_uint8(
                    v_cfg_854_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_nativeFacets_862_ = lean_ctor_get(v_cfg_854_, 6);
                v_isSharedCheck_870_ = (!lean_is_exclusive(v_cfg_854_)) as u8;
                if v_isSharedCheck_870_ == 0 {
                    v___x_864_ = v_cfg_854_;
                    v_isShared_865_ = v_isSharedCheck_870_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nativeFacets_862_);
                    lean_inc(v_extraDepTargets_860_);
                    lean_inc(v_needs_859_);
                    lean_inc(v_exeName_858_);
                    lean_inc(v_root_857_);
                    lean_inc(v_srcDir_856_);
                    lean_inc(v_toLeanConfig_855_);
                    lean_dec(v_cfg_854_);
                    v___x_864_ = lean_box(0);
                    v_isShared_865_ = v_isSharedCheck_870_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_866_ = lean_apply_1(v_f_853_, v_srcDir_856_);
                if v_isShared_865_ == 0 {
                    lean_ctor_set(v___x_864_, 1, v___x_866_);
                    v___x_868_ = v___x_864_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_869_, 0, v_toLeanConfig_855_);
                    lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_866_);
                    lean_ctor_set(v_reuseFailAlloc_869_, 2, v_root_857_);
                    lean_ctor_set(v_reuseFailAlloc_869_, 3, v_exeName_858_);
                    lean_ctor_set(v_reuseFailAlloc_869_, 4, v_needs_859_);
                    lean_ctor_set(v_reuseFailAlloc_869_, 5, v_extraDepTargets_860_);
                    lean_ctor_set(v_reuseFailAlloc_869_, 6, v_nativeFacets_862_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_869_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
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
    mut v_x_871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    v___x_872_ = l_Lake_instInhabitedLeanExeConfig_default___closed__1;
    return v___x_872_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir___proj___lam__3___boxed(
    mut v_x_873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_874_: *mut LeanObject = core::ptr::null_mut();
    v_res_874_ = l_Lake_LeanExeConfig_srcDir___proj___lam__3(v_x_873_);
    lean_dec_ref(v_x_873_);
    return v_res_874_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir___proj(
    mut v_name_884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    v___x_885_ = l_Lake_LeanExeConfig_srcDir___proj___closed__4;
    return v___x_885_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir___proj___boxed(
    mut v_name_886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_887_: *mut LeanObject = core::ptr::null_mut();
    v_res_887_ = l_Lake_LeanExeConfig_srcDir___proj(v_name_886_);
    lean_dec(v_name_886_);
    return v_res_887_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir_instConfigField(
    mut v_name_888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    v___x_889_ = l_Lake_LeanExeConfig_srcDir___proj(v_name_888_);
    return v___x_889_;
}
pub unsafe fn l_Lake_LeanExeConfig_srcDir_instConfigField___boxed(
    mut v_name_890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_891_: *mut LeanObject = core::ptr::null_mut();
    v_res_891_ = l_Lake_LeanExeConfig_srcDir_instConfigField(v_name_890_);
    lean_dec(v_name_890_);
    return v_res_891_;
}
pub unsafe fn l_Lake_LeanExeConfig_root___proj___lam__0(
    mut v_cfg_892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_893_: *mut LeanObject = core::ptr::null_mut();
    v_root_893_ = lean_ctor_get(v_cfg_892_, 2);
    lean_inc(v_root_893_);
    return v_root_893_;
}
pub unsafe fn l_Lake_LeanExeConfig_root___proj___lam__0___boxed(
    mut v_cfg_894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_895_: *mut LeanObject = core::ptr::null_mut();
    v_res_895_ = l_Lake_LeanExeConfig_root___proj___lam__0(v_cfg_894_);
    lean_dec_ref(v_cfg_894_);
    return v_res_895_;
}
pub unsafe fn l_Lake_LeanExeConfig_root___proj___lam__1(
    mut v_val_896_: *mut LeanObject,
    mut v_cfg_897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toLeanConfig_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exeName_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_needs_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_903_: u8 = 0;
    let mut v_nativeFacets_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_907_: u8 = 0;
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_911_: u8 = 0;
    let mut v_unused_912_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_898_ = lean_ctor_get(v_cfg_897_, 0);
                v_srcDir_899_ = lean_ctor_get(v_cfg_897_, 1);
                v_exeName_900_ = lean_ctor_get(v_cfg_897_, 3);
                v_needs_901_ = lean_ctor_get(v_cfg_897_, 4);
                v_extraDepTargets_902_ = lean_ctor_get(v_cfg_897_, 5);
                v_supportInterpreter_903_ = lean_ctor_get_uint8(
                    v_cfg_897_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_nativeFacets_904_ = lean_ctor_get(v_cfg_897_, 6);
                v_isSharedCheck_911_ = (!lean_is_exclusive(v_cfg_897_)) as u8;
                if v_isSharedCheck_911_ == 0 {
                    v_unused_912_ = lean_ctor_get(v_cfg_897_, 2);
                    lean_dec(v_unused_912_);
                    v___x_906_ = v_cfg_897_;
                    v_isShared_907_ = v_isSharedCheck_911_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nativeFacets_904_);
                    lean_inc(v_extraDepTargets_902_);
                    lean_inc(v_needs_901_);
                    lean_inc(v_exeName_900_);
                    lean_inc(v_srcDir_899_);
                    lean_inc(v_toLeanConfig_898_);
                    lean_dec(v_cfg_897_);
                    v___x_906_ = lean_box(0);
                    v_isShared_907_ = v_isSharedCheck_911_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_907_ == 0 {
                    lean_ctor_set(v___x_906_, 2, v_val_896_);
                    v___x_909_ = v___x_906_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_910_, 0, v_toLeanConfig_898_);
                    lean_ctor_set(v_reuseFailAlloc_910_, 1, v_srcDir_899_);
                    lean_ctor_set(v_reuseFailAlloc_910_, 2, v_val_896_);
                    lean_ctor_set(v_reuseFailAlloc_910_, 3, v_exeName_900_);
                    lean_ctor_set(v_reuseFailAlloc_910_, 4, v_needs_901_);
                    lean_ctor_set(v_reuseFailAlloc_910_, 5, v_extraDepTargets_902_);
                    lean_ctor_set(v_reuseFailAlloc_910_, 6, v_nativeFacets_904_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_910_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
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
    mut v_f_913_: *mut LeanObject,
    mut v_cfg_914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toLeanConfig_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exeName_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_needs_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_921_: u8 = 0;
    let mut v_nativeFacets_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_925_: u8 = 0;
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_915_ = lean_ctor_get(v_cfg_914_, 0);
                v_srcDir_916_ = lean_ctor_get(v_cfg_914_, 1);
                v_root_917_ = lean_ctor_get(v_cfg_914_, 2);
                v_exeName_918_ = lean_ctor_get(v_cfg_914_, 3);
                v_needs_919_ = lean_ctor_get(v_cfg_914_, 4);
                v_extraDepTargets_920_ = lean_ctor_get(v_cfg_914_, 5);
                v_supportInterpreter_921_ = lean_ctor_get_uint8(
                    v_cfg_914_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_nativeFacets_922_ = lean_ctor_get(v_cfg_914_, 6);
                v_isSharedCheck_930_ = (!lean_is_exclusive(v_cfg_914_)) as u8;
                if v_isSharedCheck_930_ == 0 {
                    v___x_924_ = v_cfg_914_;
                    v_isShared_925_ = v_isSharedCheck_930_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nativeFacets_922_);
                    lean_inc(v_extraDepTargets_920_);
                    lean_inc(v_needs_919_);
                    lean_inc(v_exeName_918_);
                    lean_inc(v_root_917_);
                    lean_inc(v_srcDir_916_);
                    lean_inc(v_toLeanConfig_915_);
                    lean_dec(v_cfg_914_);
                    v___x_924_ = lean_box(0);
                    v_isShared_925_ = v_isSharedCheck_930_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_926_ = lean_apply_1(v_f_913_, v_root_917_);
                if v_isShared_925_ == 0 {
                    lean_ctor_set(v___x_924_, 2, v___x_926_);
                    v___x_928_ = v___x_924_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_929_, 0, v_toLeanConfig_915_);
                    lean_ctor_set(v_reuseFailAlloc_929_, 1, v_srcDir_916_);
                    lean_ctor_set(v_reuseFailAlloc_929_, 2, v___x_926_);
                    lean_ctor_set(v_reuseFailAlloc_929_, 3, v_exeName_918_);
                    lean_ctor_set(v_reuseFailAlloc_929_, 4, v_needs_919_);
                    lean_ctor_set(v_reuseFailAlloc_929_, 5, v_extraDepTargets_920_);
                    lean_ctor_set(v_reuseFailAlloc_929_, 6, v_nativeFacets_922_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_929_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
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
    mut v_name_931_: *mut LeanObject,
    mut v_x_932_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_name_931_);
    return v_name_931_;
}
pub unsafe fn l_Lake_LeanExeConfig_root___proj___lam__3___boxed(
    mut v_name_933_: *mut LeanObject,
    mut v_x_934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_935_: *mut LeanObject = core::ptr::null_mut();
    v_res_935_ = l_Lake_LeanExeConfig_root___proj___lam__3(v_name_933_, v_x_934_);
    lean_dec_ref(v_x_934_);
    lean_dec(v_name_933_);
    return v_res_935_;
}
pub unsafe fn l_Lake_LeanExeConfig_root___proj(
    mut v_name_939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    v___f_940_ = l_Lake_LeanExeConfig_root___proj___closed__0;
    v___f_941_ = l_Lake_LeanExeConfig_root___proj___closed__1;
    v___f_942_ = l_Lake_LeanExeConfig_root___proj___closed__2;
    v___f_943_ = lean_alloc_closure(
        l_Lake_LeanExeConfig_root___proj___lam__3___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_943_, 0, v_name_939_);
    v___x_944_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_944_, 0, v___f_940_);
    lean_ctor_set(v___x_944_, 1, v___f_941_);
    lean_ctor_set(v___x_944_, 2, v___f_942_);
    lean_ctor_set(v___x_944_, 3, v___f_943_);
    return v___x_944_;
}
pub unsafe fn l_Lake_LeanExeConfig_root_instConfigField(
    mut v_name_945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    v___x_946_ = l_Lake_LeanExeConfig_root___proj(v_name_945_);
    return v___x_946_;
}
pub unsafe fn l_Lake_LeanExeConfig_exeName___proj___lam__0(
    mut v_cfg_947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_exeName_948_: *mut LeanObject = core::ptr::null_mut();
    v_exeName_948_ = lean_ctor_get(v_cfg_947_, 3);
    lean_inc_ref(v_exeName_948_);
    return v_exeName_948_;
}
pub unsafe fn l_Lake_LeanExeConfig_exeName___proj___lam__0___boxed(
    mut v_cfg_949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_950_: *mut LeanObject = core::ptr::null_mut();
    v_res_950_ = l_Lake_LeanExeConfig_exeName___proj___lam__0(v_cfg_949_);
    lean_dec_ref(v_cfg_949_);
    return v_res_950_;
}
pub unsafe fn l_Lake_LeanExeConfig_exeName___proj___lam__1(
    mut v_val_951_: *mut LeanObject,
    mut v_cfg_952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toLeanConfig_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_needs_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_958_: u8 = 0;
    let mut v_nativeFacets_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_962_: u8 = 0;
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_966_: u8 = 0;
    let mut v_unused_967_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_953_ = lean_ctor_get(v_cfg_952_, 0);
                v_srcDir_954_ = lean_ctor_get(v_cfg_952_, 1);
                v_root_955_ = lean_ctor_get(v_cfg_952_, 2);
                v_needs_956_ = lean_ctor_get(v_cfg_952_, 4);
                v_extraDepTargets_957_ = lean_ctor_get(v_cfg_952_, 5);
                v_supportInterpreter_958_ = lean_ctor_get_uint8(
                    v_cfg_952_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_nativeFacets_959_ = lean_ctor_get(v_cfg_952_, 6);
                v_isSharedCheck_966_ = (!lean_is_exclusive(v_cfg_952_)) as u8;
                if v_isSharedCheck_966_ == 0 {
                    v_unused_967_ = lean_ctor_get(v_cfg_952_, 3);
                    lean_dec(v_unused_967_);
                    v___x_961_ = v_cfg_952_;
                    v_isShared_962_ = v_isSharedCheck_966_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nativeFacets_959_);
                    lean_inc(v_extraDepTargets_957_);
                    lean_inc(v_needs_956_);
                    lean_inc(v_root_955_);
                    lean_inc(v_srcDir_954_);
                    lean_inc(v_toLeanConfig_953_);
                    lean_dec(v_cfg_952_);
                    v___x_961_ = lean_box(0);
                    v_isShared_962_ = v_isSharedCheck_966_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_962_ == 0 {
                    lean_ctor_set(v___x_961_, 3, v_val_951_);
                    v___x_964_ = v___x_961_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_965_, 0, v_toLeanConfig_953_);
                    lean_ctor_set(v_reuseFailAlloc_965_, 1, v_srcDir_954_);
                    lean_ctor_set(v_reuseFailAlloc_965_, 2, v_root_955_);
                    lean_ctor_set(v_reuseFailAlloc_965_, 3, v_val_951_);
                    lean_ctor_set(v_reuseFailAlloc_965_, 4, v_needs_956_);
                    lean_ctor_set(v_reuseFailAlloc_965_, 5, v_extraDepTargets_957_);
                    lean_ctor_set(v_reuseFailAlloc_965_, 6, v_nativeFacets_959_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_965_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
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
    mut v_f_968_: *mut LeanObject,
    mut v_cfg_969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toLeanConfig_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exeName_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_needs_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_976_: u8 = 0;
    let mut v_nativeFacets_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_980_: u8 = 0;
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_985_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_970_ = lean_ctor_get(v_cfg_969_, 0);
                v_srcDir_971_ = lean_ctor_get(v_cfg_969_, 1);
                v_root_972_ = lean_ctor_get(v_cfg_969_, 2);
                v_exeName_973_ = lean_ctor_get(v_cfg_969_, 3);
                v_needs_974_ = lean_ctor_get(v_cfg_969_, 4);
                v_extraDepTargets_975_ = lean_ctor_get(v_cfg_969_, 5);
                v_supportInterpreter_976_ = lean_ctor_get_uint8(
                    v_cfg_969_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_nativeFacets_977_ = lean_ctor_get(v_cfg_969_, 6);
                v_isSharedCheck_985_ = (!lean_is_exclusive(v_cfg_969_)) as u8;
                if v_isSharedCheck_985_ == 0 {
                    v___x_979_ = v_cfg_969_;
                    v_isShared_980_ = v_isSharedCheck_985_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nativeFacets_977_);
                    lean_inc(v_extraDepTargets_975_);
                    lean_inc(v_needs_974_);
                    lean_inc(v_exeName_973_);
                    lean_inc(v_root_972_);
                    lean_inc(v_srcDir_971_);
                    lean_inc(v_toLeanConfig_970_);
                    lean_dec(v_cfg_969_);
                    v___x_979_ = lean_box(0);
                    v_isShared_980_ = v_isSharedCheck_985_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_981_ = lean_apply_1(v_f_968_, v_exeName_973_);
                if v_isShared_980_ == 0 {
                    lean_ctor_set(v___x_979_, 3, v___x_981_);
                    v___x_983_ = v___x_979_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_984_, 0, v_toLeanConfig_970_);
                    lean_ctor_set(v_reuseFailAlloc_984_, 1, v_srcDir_971_);
                    lean_ctor_set(v_reuseFailAlloc_984_, 2, v_root_972_);
                    lean_ctor_set(v_reuseFailAlloc_984_, 3, v___x_981_);
                    lean_ctor_set(v_reuseFailAlloc_984_, 4, v_needs_974_);
                    lean_ctor_set(v_reuseFailAlloc_984_, 5, v_extraDepTargets_975_);
                    lean_ctor_set(v_reuseFailAlloc_984_, 6, v_nativeFacets_977_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_984_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
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
    mut v_name_986_: *mut LeanObject,
    mut v_x_987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: u8 = 0;
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_name_991_: *mut LeanObject,
    mut v_x_992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_993_: *mut LeanObject = core::ptr::null_mut();
    v_res_993_ = l_Lake_LeanExeConfig_exeName___proj___lam__3(v_name_991_, v_x_992_);
    lean_dec_ref(v_x_992_);
    return v_res_993_;
}
pub unsafe fn l_Lake_LeanExeConfig_exeName___proj(
    mut v_name_997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    v___f_998_ = l_Lake_LeanExeConfig_exeName___proj___closed__0;
    v___f_999_ = l_Lake_LeanExeConfig_exeName___proj___closed__1;
    v___f_1000_ = l_Lake_LeanExeConfig_exeName___proj___closed__2;
    v___f_1001_ = lean_alloc_closure(
        l_Lake_LeanExeConfig_exeName___proj___lam__3___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1001_, 0, v_name_997_);
    v___x_1002_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1002_, 0, v___f_998_);
    lean_ctor_set(v___x_1002_, 1, v___f_999_);
    lean_ctor_set(v___x_1002_, 2, v___f_1000_);
    lean_ctor_set(v___x_1002_, 3, v___f_1001_);
    return v___x_1002_;
}
pub unsafe fn l_Lake_LeanExeConfig_exeName_instConfigField(
    mut v_name_1003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    v___x_1004_ = l_Lake_LeanExeConfig_exeName___proj(v_name_1003_);
    return v___x_1004_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs___proj___lam__0(
    mut v_cfg_1005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_needs_1006_: *mut LeanObject = core::ptr::null_mut();
    v_needs_1006_ = lean_ctor_get(v_cfg_1005_, 4);
    lean_inc_ref(v_needs_1006_);
    return v_needs_1006_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs___proj___lam__0___boxed(
    mut v_cfg_1007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1008_: *mut LeanObject = core::ptr::null_mut();
    v_res_1008_ = l_Lake_LeanExeConfig_needs___proj___lam__0(v_cfg_1007_);
    lean_dec_ref(v_cfg_1007_);
    return v_res_1008_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs___proj___lam__1(
    mut v_val_1009_: *mut LeanObject,
    mut v_cfg_1010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toLeanConfig_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exeName_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1016_: u8 = 0;
    let mut v_nativeFacets_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1020_: u8 = 0;
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1024_: u8 = 0;
    let mut v_unused_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1011_ = lean_ctor_get(v_cfg_1010_, 0);
                v_srcDir_1012_ = lean_ctor_get(v_cfg_1010_, 1);
                v_root_1013_ = lean_ctor_get(v_cfg_1010_, 2);
                v_exeName_1014_ = lean_ctor_get(v_cfg_1010_, 3);
                v_extraDepTargets_1015_ = lean_ctor_get(v_cfg_1010_, 5);
                v_supportInterpreter_1016_ = lean_ctor_get_uint8(
                    v_cfg_1010_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1017_ = lean_ctor_get(v_cfg_1010_, 6);
                v_isSharedCheck_1024_ = (!lean_is_exclusive(v_cfg_1010_)) as u8;
                if v_isSharedCheck_1024_ == 0 {
                    v_unused_1025_ = lean_ctor_get(v_cfg_1010_, 4);
                    lean_dec(v_unused_1025_);
                    v___x_1019_ = v_cfg_1010_;
                    v_isShared_1020_ = v_isSharedCheck_1024_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nativeFacets_1017_);
                    lean_inc(v_extraDepTargets_1015_);
                    lean_inc(v_exeName_1014_);
                    lean_inc(v_root_1013_);
                    lean_inc(v_srcDir_1012_);
                    lean_inc(v_toLeanConfig_1011_);
                    lean_dec(v_cfg_1010_);
                    v___x_1019_ = lean_box(0);
                    v_isShared_1020_ = v_isSharedCheck_1024_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1020_ == 0 {
                    lean_ctor_set(v___x_1019_, 4, v_val_1009_);
                    v___x_1022_ = v___x_1019_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_toLeanConfig_1011_);
                    lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_srcDir_1012_);
                    lean_ctor_set(v_reuseFailAlloc_1023_, 2, v_root_1013_);
                    lean_ctor_set(v_reuseFailAlloc_1023_, 3, v_exeName_1014_);
                    lean_ctor_set(v_reuseFailAlloc_1023_, 4, v_val_1009_);
                    lean_ctor_set(v_reuseFailAlloc_1023_, 5, v_extraDepTargets_1015_);
                    lean_ctor_set(v_reuseFailAlloc_1023_, 6, v_nativeFacets_1017_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1023_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
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
    mut v_f_1026_: *mut LeanObject,
    mut v_cfg_1027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toLeanConfig_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exeName_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_needs_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1034_: u8 = 0;
    let mut v_nativeFacets_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1038_: u8 = 0;
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1028_ = lean_ctor_get(v_cfg_1027_, 0);
                v_srcDir_1029_ = lean_ctor_get(v_cfg_1027_, 1);
                v_root_1030_ = lean_ctor_get(v_cfg_1027_, 2);
                v_exeName_1031_ = lean_ctor_get(v_cfg_1027_, 3);
                v_needs_1032_ = lean_ctor_get(v_cfg_1027_, 4);
                v_extraDepTargets_1033_ = lean_ctor_get(v_cfg_1027_, 5);
                v_supportInterpreter_1034_ = lean_ctor_get_uint8(
                    v_cfg_1027_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1035_ = lean_ctor_get(v_cfg_1027_, 6);
                v_isSharedCheck_1043_ = (!lean_is_exclusive(v_cfg_1027_)) as u8;
                if v_isSharedCheck_1043_ == 0 {
                    v___x_1037_ = v_cfg_1027_;
                    v_isShared_1038_ = v_isSharedCheck_1043_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nativeFacets_1035_);
                    lean_inc(v_extraDepTargets_1033_);
                    lean_inc(v_needs_1032_);
                    lean_inc(v_exeName_1031_);
                    lean_inc(v_root_1030_);
                    lean_inc(v_srcDir_1029_);
                    lean_inc(v_toLeanConfig_1028_);
                    lean_dec(v_cfg_1027_);
                    v___x_1037_ = lean_box(0);
                    v_isShared_1038_ = v_isSharedCheck_1043_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1039_ = lean_apply_1(v_f_1026_, v_needs_1032_);
                if v_isShared_1038_ == 0 {
                    lean_ctor_set(v___x_1037_, 4, v___x_1039_);
                    v___x_1041_ = v___x_1037_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_toLeanConfig_1028_);
                    lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_srcDir_1029_);
                    lean_ctor_set(v_reuseFailAlloc_1042_, 2, v_root_1030_);
                    lean_ctor_set(v_reuseFailAlloc_1042_, 3, v_exeName_1031_);
                    lean_ctor_set(v_reuseFailAlloc_1042_, 4, v___x_1039_);
                    lean_ctor_set(v_reuseFailAlloc_1042_, 5, v_extraDepTargets_1033_);
                    lean_ctor_set(v_reuseFailAlloc_1042_, 6, v_nativeFacets_1035_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1042_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
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
    mut v_x_1044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    v___x_1045_ = l_Lake_instInhabitedLeanExeConfig_default___closed__3;
    return v___x_1045_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs___proj___lam__3___boxed(
    mut v_x_1046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1047_: *mut LeanObject = core::ptr::null_mut();
    v_res_1047_ = l_Lake_LeanExeConfig_needs___proj___lam__3(v_x_1046_);
    lean_dec_ref(v_x_1046_);
    return v_res_1047_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs___proj(
    mut v_name_1057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    v___x_1058_ = l_Lake_LeanExeConfig_needs___proj___closed__4;
    return v___x_1058_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs___proj___boxed(
    mut v_name_1059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1060_: *mut LeanObject = core::ptr::null_mut();
    v_res_1060_ = l_Lake_LeanExeConfig_needs___proj(v_name_1059_);
    lean_dec(v_name_1059_);
    return v_res_1060_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs_instConfigField(
    mut v_name_1061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    v___x_1062_ = l_Lake_LeanExeConfig_needs___proj(v_name_1061_);
    return v___x_1062_;
}
pub unsafe fn l_Lake_LeanExeConfig_needs_instConfigField___boxed(
    mut v_name_1063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1064_: *mut LeanObject = core::ptr::null_mut();
    v_res_1064_ = l_Lake_LeanExeConfig_needs_instConfigField(v_name_1063_);
    lean_dec(v_name_1063_);
    return v_res_1064_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets___proj___lam__0(
    mut v_cfg_1065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_extraDepTargets_1066_: *mut LeanObject = core::ptr::null_mut();
    v_extraDepTargets_1066_ = lean_ctor_get(v_cfg_1065_, 5);
    lean_inc_ref(v_extraDepTargets_1066_);
    return v_extraDepTargets_1066_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets___proj___lam__0___boxed(
    mut v_cfg_1067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1068_: *mut LeanObject = core::ptr::null_mut();
    v_res_1068_ = l_Lake_LeanExeConfig_extraDepTargets___proj___lam__0(v_cfg_1067_);
    lean_dec_ref(v_cfg_1067_);
    return v_res_1068_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets___proj___lam__1(
    mut v_val_1069_: *mut LeanObject,
    mut v_cfg_1070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toLeanConfig_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exeName_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_needs_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1076_: u8 = 0;
    let mut v_nativeFacets_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1080_: u8 = 0;
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1084_: u8 = 0;
    let mut v_unused_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1071_ = lean_ctor_get(v_cfg_1070_, 0);
                v_srcDir_1072_ = lean_ctor_get(v_cfg_1070_, 1);
                v_root_1073_ = lean_ctor_get(v_cfg_1070_, 2);
                v_exeName_1074_ = lean_ctor_get(v_cfg_1070_, 3);
                v_needs_1075_ = lean_ctor_get(v_cfg_1070_, 4);
                v_supportInterpreter_1076_ = lean_ctor_get_uint8(
                    v_cfg_1070_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1077_ = lean_ctor_get(v_cfg_1070_, 6);
                v_isSharedCheck_1084_ = (!lean_is_exclusive(v_cfg_1070_)) as u8;
                if v_isSharedCheck_1084_ == 0 {
                    v_unused_1085_ = lean_ctor_get(v_cfg_1070_, 5);
                    lean_dec(v_unused_1085_);
                    v___x_1079_ = v_cfg_1070_;
                    v_isShared_1080_ = v_isSharedCheck_1084_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nativeFacets_1077_);
                    lean_inc(v_needs_1075_);
                    lean_inc(v_exeName_1074_);
                    lean_inc(v_root_1073_);
                    lean_inc(v_srcDir_1072_);
                    lean_inc(v_toLeanConfig_1071_);
                    lean_dec(v_cfg_1070_);
                    v___x_1079_ = lean_box(0);
                    v_isShared_1080_ = v_isSharedCheck_1084_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1080_ == 0 {
                    lean_ctor_set(v___x_1079_, 5, v_val_1069_);
                    v___x_1082_ = v___x_1079_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_toLeanConfig_1071_);
                    lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_srcDir_1072_);
                    lean_ctor_set(v_reuseFailAlloc_1083_, 2, v_root_1073_);
                    lean_ctor_set(v_reuseFailAlloc_1083_, 3, v_exeName_1074_);
                    lean_ctor_set(v_reuseFailAlloc_1083_, 4, v_needs_1075_);
                    lean_ctor_set(v_reuseFailAlloc_1083_, 5, v_val_1069_);
                    lean_ctor_set(v_reuseFailAlloc_1083_, 6, v_nativeFacets_1077_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1083_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
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
    mut v_f_1086_: *mut LeanObject,
    mut v_cfg_1087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toLeanConfig_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exeName_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_needs_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1094_: u8 = 0;
    let mut v_nativeFacets_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1098_: u8 = 0;
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1103_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1088_ = lean_ctor_get(v_cfg_1087_, 0);
                v_srcDir_1089_ = lean_ctor_get(v_cfg_1087_, 1);
                v_root_1090_ = lean_ctor_get(v_cfg_1087_, 2);
                v_exeName_1091_ = lean_ctor_get(v_cfg_1087_, 3);
                v_needs_1092_ = lean_ctor_get(v_cfg_1087_, 4);
                v_extraDepTargets_1093_ = lean_ctor_get(v_cfg_1087_, 5);
                v_supportInterpreter_1094_ = lean_ctor_get_uint8(
                    v_cfg_1087_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1095_ = lean_ctor_get(v_cfg_1087_, 6);
                v_isSharedCheck_1103_ = (!lean_is_exclusive(v_cfg_1087_)) as u8;
                if v_isSharedCheck_1103_ == 0 {
                    v___x_1097_ = v_cfg_1087_;
                    v_isShared_1098_ = v_isSharedCheck_1103_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nativeFacets_1095_);
                    lean_inc(v_extraDepTargets_1093_);
                    lean_inc(v_needs_1092_);
                    lean_inc(v_exeName_1091_);
                    lean_inc(v_root_1090_);
                    lean_inc(v_srcDir_1089_);
                    lean_inc(v_toLeanConfig_1088_);
                    lean_dec(v_cfg_1087_);
                    v___x_1097_ = lean_box(0);
                    v_isShared_1098_ = v_isSharedCheck_1103_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1099_ = lean_apply_1(v_f_1086_, v_extraDepTargets_1093_);
                if v_isShared_1098_ == 0 {
                    lean_ctor_set(v___x_1097_, 5, v___x_1099_);
                    v___x_1101_ = v___x_1097_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_toLeanConfig_1088_);
                    lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_srcDir_1089_);
                    lean_ctor_set(v_reuseFailAlloc_1102_, 2, v_root_1090_);
                    lean_ctor_set(v_reuseFailAlloc_1102_, 3, v_exeName_1091_);
                    lean_ctor_set(v_reuseFailAlloc_1102_, 4, v_needs_1092_);
                    lean_ctor_set(v_reuseFailAlloc_1102_, 5, v___x_1099_);
                    lean_ctor_set(v_reuseFailAlloc_1102_, 6, v_nativeFacets_1095_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1102_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
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
    mut v_x_1106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    v___x_1107_ = l_Lake_LeanExeConfig_extraDepTargets___proj___lam__3___closed__0;
    return v___x_1107_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets___proj___lam__3___boxed(
    mut v_x_1108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1109_: *mut LeanObject = core::ptr::null_mut();
    v_res_1109_ = l_Lake_LeanExeConfig_extraDepTargets___proj___lam__3(v_x_1108_);
    lean_dec_ref(v_x_1108_);
    return v_res_1109_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets___proj(
    mut v_name_1119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    v___x_1120_ = l_Lake_LeanExeConfig_extraDepTargets___proj___closed__4;
    return v___x_1120_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets___proj___boxed(
    mut v_name_1121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1122_: *mut LeanObject = core::ptr::null_mut();
    v_res_1122_ = l_Lake_LeanExeConfig_extraDepTargets___proj(v_name_1121_);
    lean_dec(v_name_1121_);
    return v_res_1122_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets_instConfigField(
    mut v_name_1123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    v___x_1124_ = l_Lake_LeanExeConfig_extraDepTargets___proj(v_name_1123_);
    return v___x_1124_;
}
pub unsafe fn l_Lake_LeanExeConfig_extraDepTargets_instConfigField___boxed(
    mut v_name_1125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1126_: *mut LeanObject = core::ptr::null_mut();
    v_res_1126_ = l_Lake_LeanExeConfig_extraDepTargets_instConfigField(v_name_1125_);
    lean_dec(v_name_1125_);
    return v_res_1126_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___lam__0(
    mut v_cfg_1127_: *mut LeanObject,
) -> u8 {
    let mut v_supportInterpreter_1128_: u8 = 0;
    v_supportInterpreter_1128_ = lean_ctor_get_uint8(
        v_cfg_1127_,
        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
    );
    return v_supportInterpreter_1128_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___lam__0___boxed(
    mut v_cfg_1129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1130_: u8 = 0;
    let mut v_r_1131_: *mut LeanObject = core::ptr::null_mut();
    v_res_1130_ = l_Lake_LeanExeConfig_supportInterpreter___proj___lam__0(v_cfg_1129_);
    lean_dec_ref(v_cfg_1129_);
    v_r_1131_ = lean_box((v_res_1130_) as usize);
    return v_r_1131_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___lam__1(
    mut v_val_1132_: u8,
    mut v_cfg_1133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toLeanConfig_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exeName_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_needs_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1143_: u8 = 0;
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1147_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1134_ = lean_ctor_get(v_cfg_1133_, 0);
                v_srcDir_1135_ = lean_ctor_get(v_cfg_1133_, 1);
                v_root_1136_ = lean_ctor_get(v_cfg_1133_, 2);
                v_exeName_1137_ = lean_ctor_get(v_cfg_1133_, 3);
                v_needs_1138_ = lean_ctor_get(v_cfg_1133_, 4);
                v_extraDepTargets_1139_ = lean_ctor_get(v_cfg_1133_, 5);
                v_nativeFacets_1140_ = lean_ctor_get(v_cfg_1133_, 6);
                v_isSharedCheck_1147_ = (!lean_is_exclusive(v_cfg_1133_)) as u8;
                if v_isSharedCheck_1147_ == 0 {
                    v___x_1142_ = v_cfg_1133_;
                    v_isShared_1143_ = v_isSharedCheck_1147_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nativeFacets_1140_);
                    lean_inc(v_extraDepTargets_1139_);
                    lean_inc(v_needs_1138_);
                    lean_inc(v_exeName_1137_);
                    lean_inc(v_root_1136_);
                    lean_inc(v_srcDir_1135_);
                    lean_inc(v_toLeanConfig_1134_);
                    lean_dec(v_cfg_1133_);
                    v___x_1142_ = lean_box(0);
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
                    v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_toLeanConfig_1134_);
                    lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_srcDir_1135_);
                    lean_ctor_set(v_reuseFailAlloc_1146_, 2, v_root_1136_);
                    lean_ctor_set(v_reuseFailAlloc_1146_, 3, v_exeName_1137_);
                    lean_ctor_set(v_reuseFailAlloc_1146_, 4, v_needs_1138_);
                    lean_ctor_set(v_reuseFailAlloc_1146_, 5, v_extraDepTargets_1139_);
                    lean_ctor_set(v_reuseFailAlloc_1146_, 6, v_nativeFacets_1140_);
                    v___x_1145_ = v_reuseFailAlloc_1146_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_1145_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_val_1132_,
                );
                return v___x_1145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___lam__1___boxed(
    mut v_val_1148_: *mut LeanObject,
    mut v_cfg_1149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_59__boxed_1150_: u8 = 0;
    let mut v_res_1151_: *mut LeanObject = core::ptr::null_mut();
    v_val_59__boxed_1150_ = (lean_unbox(v_val_1148_) as u8);
    v_res_1151_ =
        l_Lake_LeanExeConfig_supportInterpreter___proj___lam__1(v_val_59__boxed_1150_, v_cfg_1149_);
    return v_res_1151_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___lam__2(
    mut v_f_1152_: *mut LeanObject,
    mut v_cfg_1153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toLeanConfig_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exeName_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_needs_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1160_: u8 = 0;
    let mut v_nativeFacets_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1164_: u8 = 0;
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: u8 = 0;
    let mut v_reuseFailAlloc_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1171_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1154_ = lean_ctor_get(v_cfg_1153_, 0);
                v_srcDir_1155_ = lean_ctor_get(v_cfg_1153_, 1);
                v_root_1156_ = lean_ctor_get(v_cfg_1153_, 2);
                v_exeName_1157_ = lean_ctor_get(v_cfg_1153_, 3);
                v_needs_1158_ = lean_ctor_get(v_cfg_1153_, 4);
                v_extraDepTargets_1159_ = lean_ctor_get(v_cfg_1153_, 5);
                v_supportInterpreter_1160_ = lean_ctor_get_uint8(
                    v_cfg_1153_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1161_ = lean_ctor_get(v_cfg_1153_, 6);
                v_isSharedCheck_1171_ = (!lean_is_exclusive(v_cfg_1153_)) as u8;
                if v_isSharedCheck_1171_ == 0 {
                    v___x_1163_ = v_cfg_1153_;
                    v_isShared_1164_ = v_isSharedCheck_1171_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nativeFacets_1161_);
                    lean_inc(v_extraDepTargets_1159_);
                    lean_inc(v_needs_1158_);
                    lean_inc(v_exeName_1157_);
                    lean_inc(v_root_1156_);
                    lean_inc(v_srcDir_1155_);
                    lean_inc(v_toLeanConfig_1154_);
                    lean_dec(v_cfg_1153_);
                    v___x_1163_ = lean_box(0);
                    v_isShared_1164_ = v_isSharedCheck_1171_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1165_ = lean_box((v_supportInterpreter_1160_) as usize);
                v___x_1166_ = lean_apply_1(v_f_1152_, v___x_1165_);
                if v_isShared_1164_ == 0 {
                    v___x_1168_ = v___x_1163_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_toLeanConfig_1154_);
                    lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_srcDir_1155_);
                    lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_root_1156_);
                    lean_ctor_set(v_reuseFailAlloc_1170_, 3, v_exeName_1157_);
                    lean_ctor_set(v_reuseFailAlloc_1170_, 4, v_needs_1158_);
                    lean_ctor_set(v_reuseFailAlloc_1170_, 5, v_extraDepTargets_1159_);
                    lean_ctor_set(v_reuseFailAlloc_1170_, 6, v_nativeFacets_1161_);
                    v___x_1168_ = v_reuseFailAlloc_1170_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1169_ = (lean_unbox(v___x_1166_) as u8);
                lean_ctor_set_uint8(
                    v___x_1168_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v___x_1169_,
                );
                return v___x_1168_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___lam__3(
    mut v_x_1172_: *mut LeanObject,
) -> u8 {
    let mut v___x_1173_: u8 = 0;
    v___x_1173_ = 0;
    return v___x_1173_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___lam__3___boxed(
    mut v_x_1174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1175_: u8 = 0;
    let mut v_r_1176_: *mut LeanObject = core::ptr::null_mut();
    v_res_1175_ = l_Lake_LeanExeConfig_supportInterpreter___proj___lam__3(v_x_1174_);
    lean_dec_ref(v_x_1174_);
    v_r_1176_ = lean_box((v_res_1175_) as usize);
    return v_r_1176_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj(
    mut v_name_1186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    v___x_1187_ = l_Lake_LeanExeConfig_supportInterpreter___proj___closed__4;
    return v___x_1187_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter___proj___boxed(
    mut v_name_1188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1189_: *mut LeanObject = core::ptr::null_mut();
    v_res_1189_ = l_Lake_LeanExeConfig_supportInterpreter___proj(v_name_1188_);
    lean_dec(v_name_1188_);
    return v_res_1189_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter_instConfigField(
    mut v_name_1190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    v___x_1191_ = l_Lake_LeanExeConfig_supportInterpreter___proj(v_name_1190_);
    return v___x_1191_;
}
pub unsafe fn l_Lake_LeanExeConfig_supportInterpreter_instConfigField___boxed(
    mut v_name_1192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1193_: *mut LeanObject = core::ptr::null_mut();
    v_res_1193_ = l_Lake_LeanExeConfig_supportInterpreter_instConfigField(v_name_1192_);
    lean_dec(v_name_1192_);
    return v_res_1193_;
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets___proj___lam__0(
    mut v_cfg_1194_: *mut LeanObject,
    mut v___y_1195_: u8,
) -> *mut LeanObject {
    let mut v_nativeFacets_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    v_nativeFacets_1196_ = lean_ctor_get(v_cfg_1194_, 6);
    lean_inc_ref(v_nativeFacets_1196_);
    lean_dec_ref(v_cfg_1194_);
    v___x_1197_ = lean_box((v___y_1195_) as usize);
    v___x_1198_ = lean_apply_1(v_nativeFacets_1196_, v___x_1197_);
    return v___x_1198_;
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets___proj___lam__0___boxed(
    mut v_cfg_1199_: *mut LeanObject,
    mut v___y_1200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_135__boxed_1201_: u8 = 0;
    let mut v_res_1202_: *mut LeanObject = core::ptr::null_mut();
    v___y_135__boxed_1201_ = (lean_unbox(v___y_1200_) as u8);
    v_res_1202_ =
        l_Lake_LeanExeConfig_nativeFacets___proj___lam__0(v_cfg_1199_, v___y_135__boxed_1201_);
    return v_res_1202_;
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets___proj___lam__1(
    mut v_val_1203_: *mut LeanObject,
    mut v_cfg_1204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toLeanConfig_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exeName_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_needs_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1211_: u8 = 0;
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1214_: u8 = 0;
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1218_: u8 = 0;
    let mut v_unused_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1205_ = lean_ctor_get(v_cfg_1204_, 0);
                v_srcDir_1206_ = lean_ctor_get(v_cfg_1204_, 1);
                v_root_1207_ = lean_ctor_get(v_cfg_1204_, 2);
                v_exeName_1208_ = lean_ctor_get(v_cfg_1204_, 3);
                v_needs_1209_ = lean_ctor_get(v_cfg_1204_, 4);
                v_extraDepTargets_1210_ = lean_ctor_get(v_cfg_1204_, 5);
                v_supportInterpreter_1211_ = lean_ctor_get_uint8(
                    v_cfg_1204_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_isSharedCheck_1218_ = (!lean_is_exclusive(v_cfg_1204_)) as u8;
                if v_isSharedCheck_1218_ == 0 {
                    v_unused_1219_ = lean_ctor_get(v_cfg_1204_, 6);
                    lean_dec(v_unused_1219_);
                    v___x_1213_ = v_cfg_1204_;
                    v_isShared_1214_ = v_isSharedCheck_1218_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_extraDepTargets_1210_);
                    lean_inc(v_needs_1209_);
                    lean_inc(v_exeName_1208_);
                    lean_inc(v_root_1207_);
                    lean_inc(v_srcDir_1206_);
                    lean_inc(v_toLeanConfig_1205_);
                    lean_dec(v_cfg_1204_);
                    v___x_1213_ = lean_box(0);
                    v_isShared_1214_ = v_isSharedCheck_1218_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1214_ == 0 {
                    lean_ctor_set(v___x_1213_, 6, v_val_1203_);
                    v___x_1216_ = v___x_1213_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_toLeanConfig_1205_);
                    lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_srcDir_1206_);
                    lean_ctor_set(v_reuseFailAlloc_1217_, 2, v_root_1207_);
                    lean_ctor_set(v_reuseFailAlloc_1217_, 3, v_exeName_1208_);
                    lean_ctor_set(v_reuseFailAlloc_1217_, 4, v_needs_1209_);
                    lean_ctor_set(v_reuseFailAlloc_1217_, 5, v_extraDepTargets_1210_);
                    lean_ctor_set(v_reuseFailAlloc_1217_, 6, v_val_1203_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1217_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
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
    mut v_f_1220_: *mut LeanObject,
    mut v_cfg_1221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toLeanConfig_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exeName_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_needs_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1228_: u8 = 0;
    let mut v_nativeFacets_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1232_: u8 = 0;
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1222_ = lean_ctor_get(v_cfg_1221_, 0);
                v_srcDir_1223_ = lean_ctor_get(v_cfg_1221_, 1);
                v_root_1224_ = lean_ctor_get(v_cfg_1221_, 2);
                v_exeName_1225_ = lean_ctor_get(v_cfg_1221_, 3);
                v_needs_1226_ = lean_ctor_get(v_cfg_1221_, 4);
                v_extraDepTargets_1227_ = lean_ctor_get(v_cfg_1221_, 5);
                v_supportInterpreter_1228_ = lean_ctor_get_uint8(
                    v_cfg_1221_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1229_ = lean_ctor_get(v_cfg_1221_, 6);
                v_isSharedCheck_1237_ = (!lean_is_exclusive(v_cfg_1221_)) as u8;
                if v_isSharedCheck_1237_ == 0 {
                    v___x_1231_ = v_cfg_1221_;
                    v_isShared_1232_ = v_isSharedCheck_1237_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nativeFacets_1229_);
                    lean_inc(v_extraDepTargets_1227_);
                    lean_inc(v_needs_1226_);
                    lean_inc(v_exeName_1225_);
                    lean_inc(v_root_1224_);
                    lean_inc(v_srcDir_1223_);
                    lean_inc(v_toLeanConfig_1222_);
                    lean_dec(v_cfg_1221_);
                    v___x_1231_ = lean_box(0);
                    v_isShared_1232_ = v_isSharedCheck_1237_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1233_ = lean_apply_1(v_f_1220_, v_nativeFacets_1229_);
                if v_isShared_1232_ == 0 {
                    lean_ctor_set(v___x_1231_, 6, v___x_1233_);
                    v___x_1235_ = v___x_1231_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_toLeanConfig_1222_);
                    lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_srcDir_1223_);
                    lean_ctor_set(v_reuseFailAlloc_1236_, 2, v_root_1224_);
                    lean_ctor_set(v_reuseFailAlloc_1236_, 3, v_exeName_1225_);
                    lean_ctor_set(v_reuseFailAlloc_1236_, 4, v_needs_1226_);
                    lean_ctor_set(v_reuseFailAlloc_1236_, 5, v_extraDepTargets_1227_);
                    lean_ctor_set(v_reuseFailAlloc_1236_, 6, v___x_1233_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1236_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
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
    mut v_x_1238_: *mut LeanObject,
    mut v___y_1239_: u8,
) -> *mut LeanObject {
    let mut v___y_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
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
                v___x_1242_ = lean_unsigned_to_nat(1);
                v___x_1243_ = lean_mk_empty_array_with_capacity(v___x_1242_);
                lean_inc(v___y_1241_);
                v___x_1244_ = lean_array_push(v___x_1243_, v___y_1241_);
                return v___x_1244_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets___proj___lam__3___boxed(
    mut v_x_1247_: *mut LeanObject,
    mut v___y_1248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_185__boxed_1249_: u8 = 0;
    let mut v_res_1250_: *mut LeanObject = core::ptr::null_mut();
    v___y_185__boxed_1249_ = (lean_unbox(v___y_1248_) as u8);
    v_res_1250_ =
        l_Lake_LeanExeConfig_nativeFacets___proj___lam__3(v_x_1247_, v___y_185__boxed_1249_);
    lean_dec_ref(v_x_1247_);
    return v_res_1250_;
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets___proj(
    mut v_name_1260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    v___x_1261_ = l_Lake_LeanExeConfig_nativeFacets___proj___closed__4;
    return v___x_1261_;
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets___proj___boxed(
    mut v_name_1262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1263_: *mut LeanObject = core::ptr::null_mut();
    v_res_1263_ = l_Lake_LeanExeConfig_nativeFacets___proj(v_name_1262_);
    lean_dec(v_name_1262_);
    return v_res_1263_;
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets_instConfigField(
    mut v_name_1264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    v___x_1265_ = l_Lake_LeanExeConfig_nativeFacets___proj(v_name_1264_);
    return v___x_1265_;
}
pub unsafe fn l_Lake_LeanExeConfig_nativeFacets_instConfigField___boxed(
    mut v_name_1266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1267_: *mut LeanObject = core::ptr::null_mut();
    v_res_1267_ = l_Lake_LeanExeConfig_nativeFacets_instConfigField(v_name_1266_);
    lean_dec(v_name_1266_);
    return v_res_1267_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig___proj___lam__0(
    mut v_cfg_1268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toLeanConfig_1269_: *mut LeanObject = core::ptr::null_mut();
    v_toLeanConfig_1269_ = lean_ctor_get(v_cfg_1268_, 0);
    lean_inc_ref(v_toLeanConfig_1269_);
    return v_toLeanConfig_1269_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig___proj___lam__0___boxed(
    mut v_cfg_1270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1271_: *mut LeanObject = core::ptr::null_mut();
    v_res_1271_ = l_Lake_LeanExeConfig_toLeanConfig___proj___lam__0(v_cfg_1270_);
    lean_dec_ref(v_cfg_1270_);
    return v_res_1271_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig___proj___lam__1(
    mut v_val_1272_: *mut LeanObject,
    mut v_cfg_1273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_srcDir_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exeName_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_needs_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1279_: u8 = 0;
    let mut v_nativeFacets_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1283_: u8 = 0;
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1287_: u8 = 0;
    let mut v_unused_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_srcDir_1274_ = lean_ctor_get(v_cfg_1273_, 1);
                v_root_1275_ = lean_ctor_get(v_cfg_1273_, 2);
                v_exeName_1276_ = lean_ctor_get(v_cfg_1273_, 3);
                v_needs_1277_ = lean_ctor_get(v_cfg_1273_, 4);
                v_extraDepTargets_1278_ = lean_ctor_get(v_cfg_1273_, 5);
                v_supportInterpreter_1279_ = lean_ctor_get_uint8(
                    v_cfg_1273_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1280_ = lean_ctor_get(v_cfg_1273_, 6);
                v_isSharedCheck_1287_ = (!lean_is_exclusive(v_cfg_1273_)) as u8;
                if v_isSharedCheck_1287_ == 0 {
                    v_unused_1288_ = lean_ctor_get(v_cfg_1273_, 0);
                    lean_dec(v_unused_1288_);
                    v___x_1282_ = v_cfg_1273_;
                    v_isShared_1283_ = v_isSharedCheck_1287_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nativeFacets_1280_);
                    lean_inc(v_extraDepTargets_1278_);
                    lean_inc(v_needs_1277_);
                    lean_inc(v_exeName_1276_);
                    lean_inc(v_root_1275_);
                    lean_inc(v_srcDir_1274_);
                    lean_dec(v_cfg_1273_);
                    v___x_1282_ = lean_box(0);
                    v_isShared_1283_ = v_isSharedCheck_1287_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1283_ == 0 {
                    lean_ctor_set(v___x_1282_, 0, v_val_1272_);
                    v___x_1285_ = v___x_1282_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_val_1272_);
                    lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_srcDir_1274_);
                    lean_ctor_set(v_reuseFailAlloc_1286_, 2, v_root_1275_);
                    lean_ctor_set(v_reuseFailAlloc_1286_, 3, v_exeName_1276_);
                    lean_ctor_set(v_reuseFailAlloc_1286_, 4, v_needs_1277_);
                    lean_ctor_set(v_reuseFailAlloc_1286_, 5, v_extraDepTargets_1278_);
                    lean_ctor_set(v_reuseFailAlloc_1286_, 6, v_nativeFacets_1280_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1286_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
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
    mut v_f_1289_: *mut LeanObject,
    mut v_cfg_1290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toLeanConfig_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exeName_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_needs_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_supportInterpreter_1297_: u8 = 0;
    let mut v_nativeFacets_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1301_: u8 = 0;
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1306_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLeanConfig_1291_ = lean_ctor_get(v_cfg_1290_, 0);
                v_srcDir_1292_ = lean_ctor_get(v_cfg_1290_, 1);
                v_root_1293_ = lean_ctor_get(v_cfg_1290_, 2);
                v_exeName_1294_ = lean_ctor_get(v_cfg_1290_, 3);
                v_needs_1295_ = lean_ctor_get(v_cfg_1290_, 4);
                v_extraDepTargets_1296_ = lean_ctor_get(v_cfg_1290_, 5);
                v_supportInterpreter_1297_ = lean_ctor_get_uint8(
                    v_cfg_1290_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_nativeFacets_1298_ = lean_ctor_get(v_cfg_1290_, 6);
                v_isSharedCheck_1306_ = (!lean_is_exclusive(v_cfg_1290_)) as u8;
                if v_isSharedCheck_1306_ == 0 {
                    v___x_1300_ = v_cfg_1290_;
                    v_isShared_1301_ = v_isSharedCheck_1306_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nativeFacets_1298_);
                    lean_inc(v_extraDepTargets_1296_);
                    lean_inc(v_needs_1295_);
                    lean_inc(v_exeName_1294_);
                    lean_inc(v_root_1293_);
                    lean_inc(v_srcDir_1292_);
                    lean_inc(v_toLeanConfig_1291_);
                    lean_dec(v_cfg_1290_);
                    v___x_1300_ = lean_box(0);
                    v_isShared_1301_ = v_isSharedCheck_1306_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1302_ = lean_apply_1(v_f_1289_, v_toLeanConfig_1291_);
                if v_isShared_1301_ == 0 {
                    lean_ctor_set(v___x_1300_, 0, v___x_1302_);
                    v___x_1304_ = v___x_1300_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
                    lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_srcDir_1292_);
                    lean_ctor_set(v_reuseFailAlloc_1305_, 2, v_root_1293_);
                    lean_ctor_set(v_reuseFailAlloc_1305_, 3, v_exeName_1294_);
                    lean_ctor_set(v_reuseFailAlloc_1305_, 4, v_needs_1295_);
                    lean_ctor_set(v_reuseFailAlloc_1305_, 5, v_extraDepTargets_1296_);
                    lean_ctor_set(v_reuseFailAlloc_1305_, 6, v_nativeFacets_1298_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1305_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
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
    mut v_x_1314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    v___x_1315_ = l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__1;
    return v___x_1315_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___boxed(
    mut v_x_1316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1317_: *mut LeanObject = core::ptr::null_mut();
    v_res_1317_ = l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3(v_x_1316_);
    lean_dec_ref(v_x_1316_);
    return v_res_1317_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig___proj(
    mut v_name_1327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    v___x_1328_ = l_Lake_LeanExeConfig_toLeanConfig___proj___closed__4;
    return v___x_1328_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig___proj___boxed(
    mut v_name_1329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1330_: *mut LeanObject = core::ptr::null_mut();
    v_res_1330_ = l_Lake_LeanExeConfig_toLeanConfig___proj(v_name_1329_);
    lean_dec(v_name_1329_);
    return v_res_1330_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig_instConfigParent(
    mut v_name_1331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    v___x_1332_ = l_Lake_LeanExeConfig_toLeanConfig___proj(v_name_1331_);
    return v___x_1332_;
}
pub unsafe fn l_Lake_LeanExeConfig_toLeanConfig_instConfigParent___boxed(
    mut v_name_1333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1334_: *mut LeanObject = core::ptr::null_mut();
    v_res_1334_ = l_Lake_LeanExeConfig_toLeanConfig_instConfigParent(v_name_1333_);
    lean_dec(v_name_1333_);
    return v_res_1334_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__4() -> *mut LeanObject {
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    v___x_1344_ = l_Lake_LeanExeConfig___fields___closed__3;
    v___x_1345_ = l_Lake_LeanExeConfig___fields___closed__0;
    v___x_1346_ = lean_array_push(v___x_1345_, v___x_1344_);
    return v___x_1346_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__8() -> *mut LeanObject {
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    v___x_1354_ = l_Lake_LeanExeConfig___fields___closed__7;
    v___x_1355_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__4),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__4_once),
        _init_l_Lake_LeanExeConfig___fields___closed__4,
    );
    v___x_1356_ = lean_array_push(v___x_1355_, v___x_1354_);
    return v___x_1356_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__12() -> *mut LeanObject {
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    v___x_1364_ = l_Lake_LeanExeConfig___fields___closed__11;
    v___x_1365_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__8),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__8_once),
        _init_l_Lake_LeanExeConfig___fields___closed__8,
    );
    v___x_1366_ = lean_array_push(v___x_1365_, v___x_1364_);
    return v___x_1366_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__16() -> *mut LeanObject {
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    v___x_1374_ = l_Lake_LeanExeConfig___fields___closed__15;
    v___x_1375_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__12),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__12_once),
        _init_l_Lake_LeanExeConfig___fields___closed__12,
    );
    v___x_1376_ = lean_array_push(v___x_1375_, v___x_1374_);
    return v___x_1376_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__20() -> *mut LeanObject {
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    v___x_1384_ = l_Lake_LeanExeConfig___fields___closed__19;
    v___x_1385_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__16),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__16_once),
        _init_l_Lake_LeanExeConfig___fields___closed__16,
    );
    v___x_1386_ = lean_array_push(v___x_1385_, v___x_1384_);
    return v___x_1386_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__24() -> *mut LeanObject {
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    v___x_1394_ = l_Lake_LeanExeConfig___fields___closed__23;
    v___x_1395_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__20),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__20_once),
        _init_l_Lake_LeanExeConfig___fields___closed__20,
    );
    v___x_1396_ = lean_array_push(v___x_1395_, v___x_1394_);
    return v___x_1396_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__28() -> *mut LeanObject {
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    v___x_1404_ = l_Lake_LeanExeConfig___fields___closed__27;
    v___x_1405_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__24),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__24_once),
        _init_l_Lake_LeanExeConfig___fields___closed__24,
    );
    v___x_1406_ = lean_array_push(v___x_1405_, v___x_1404_);
    return v___x_1406_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__29() -> *mut LeanObject {
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    v___x_1407_ = l_Lake_LeanConfig___fields;
    v___x_1408_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__28),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__28_once),
        _init_l_Lake_LeanExeConfig___fields___closed__28,
    );
    v___x_1409_ = l_Array_append___redArg(v___x_1408_, v___x_1407_);
    return v___x_1409_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields___closed__33() -> *mut LeanObject {
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    v___x_1417_ = l_Lake_LeanExeConfig___fields___closed__32;
    v___x_1418_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__29),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__29_once),
        _init_l_Lake_LeanExeConfig___fields___closed__29,
    );
    v___x_1419_ = lean_array_push(v___x_1418_, v___x_1417_);
    return v___x_1419_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig___fields() -> *mut LeanObject {
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    v___x_1420_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__33),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig___fields___closed__33_once),
        _init_l_Lake_LeanExeConfig___fields___closed__33,
    );
    return v___x_1420_;
}
pub unsafe fn l_Lake_LeanExeConfig_instConfigFields(
    mut v_name_1421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    v___x_1422_ = l_Lake_LeanExeConfig___fields;
    return v___x_1422_;
}
pub unsafe fn l_Lake_LeanExeConfig_instConfigFields___boxed(
    mut v_name_1423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1424_: *mut LeanObject = core::ptr::null_mut();
    v_res_1424_ = l_Lake_LeanExeConfig_instConfigFields(v_name_1423_);
    lean_dec(v_name_1423_);
    return v_res_1424_;
}
pub unsafe fn l_Lake_LeanExeConfig_instConfigInfo___lam__0(
    mut v_x1_1425_: *mut LeanObject,
    mut v_x2_1426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    v_name_1427_ = lean_ctor_get(v_x2_1426_, 0);
    lean_inc(v_name_1427_);
    v___x_1428_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_name_1427_,
        v_x2_1426_,
        v_x1_1425_,
    );
    return v___x_1428_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig_instConfigInfo___closed__0() -> *mut LeanObject {
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    v___x_1429_ = l_Lake_LeanExeConfig___fields;
    v___x_1430_ = lean_array_get_size(v___x_1429_);
    return v___x_1430_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig_instConfigInfo___closed__11() -> u8 {
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: u8 = 0;
    v___x_1450_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_LeanExeConfig_instConfigInfo___closed__0,
    );
    v___x_1451_ = lean_unsigned_to_nat(0);
    v___x_1452_ = lean_nat_dec_lt(v___x_1451_, v___x_1450_);
    return v___x_1452_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig_instConfigInfo___closed__13() -> u8 {
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: u8 = 0;
    v___x_1454_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_LeanExeConfig_instConfigInfo___closed__0,
    );
    v___x_1455_ = lean_nat_dec_le(v___x_1454_, v___x_1454_);
    return v___x_1455_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig_instConfigInfo___closed__14() -> usize {
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: usize = 0;
    v___x_1456_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_LeanExeConfig_instConfigInfo___closed__0,
    );
    v___x_1457_ = lean_usize_of_nat(v___x_1456_);
    return v___x_1457_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig_instConfigInfo___closed__15() -> *mut LeanObject {
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: usize = 0;
    let mut v___x_1460_: usize = 0;
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    v___x_1458_ = lean_box(1);
    v___x_1459_ = lean_usize_once(
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__14),
        core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__14_once),
        _init_l_Lake_LeanExeConfig_instConfigInfo___closed__14,
    );
    v___x_1460_ = 0usize;
    v___x_1461_ = l_Lake_LeanExeConfig___fields;
    v___f_1462_ = l_Lake_LeanExeConfig_instConfigInfo___closed__12;
    v___x_1463_ = l_Lake_LeanExeConfig_instConfigInfo___closed__10;
    v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_1463_,
        v___f_1462_,
        v___x_1461_,
        v___x_1460_,
        v___x_1459_,
        v___x_1458_,
    );
    return v___x_1464_;
}
pub unsafe fn _init_l_Lake_LeanExeConfig_instConfigInfo() -> *mut LeanObject {
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: u8 = 0;
    let mut v___x_1472_: u8 = 0;
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1465_ = l_Lake_LeanExeConfig___fields;
                v___x_1470_ = lean_box(1);
                v___x_1471_ = lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__11),
                    core::ptr::addr_of_mut!(l_Lake_LeanExeConfig_instConfigInfo___closed__11_once),
                    _init_l_Lake_LeanExeConfig_instConfigInfo___closed__11,
                );
                if v___x_1471_ == 0 {
                    v___y_1467_ = v___x_1470_;
                    state = 1;
                    continue;
                } else {
                    v___x_1472_ = lean_uint8_once(
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
                            v___x_1473_ = lean_obj_once(
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
                        v___x_1474_ = lean_obj_once(
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
                v___x_1468_ = lean_unsigned_to_nat(1);
                lean_inc(v___y_1467_);
                v___x_1469_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1469_, 0, v___x_1465_);
                lean_ctor_set(v___x_1469_, 1, v___y_1467_);
                lean_ctor_set(v___x_1469_, 2, v___x_1468_);
                return v___x_1469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanExeConfig_instEmptyCollection___lam__1(
    mut v___x_1475_: u8,
    mut v_x_1476_: *mut LeanObject,
) -> u8 {
    return v___x_1475_;
}
pub unsafe fn l_Lake_LeanExeConfig_instEmptyCollection___lam__1___boxed(
    mut v___x_1477_: *mut LeanObject,
    mut v_x_1478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_83__boxed_1479_: u8 = 0;
    let mut v_res_1480_: u8 = 0;
    let mut v_r_1481_: *mut LeanObject = core::ptr::null_mut();
    v___x_83__boxed_1479_ = (lean_unbox(v___x_1477_) as u8);
    v_res_1480_ =
        l_Lake_LeanExeConfig_instEmptyCollection___lam__1(v___x_83__boxed_1479_, v_x_1478_);
    lean_dec_ref(v_x_1478_);
    v_r_1481_ = lean_box((v_res_1480_) as usize);
    return v_r_1481_;
}
pub unsafe fn l_Lake_LeanExeConfig_instEmptyCollection(
    mut v_name_1485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: u8 = 0;
    let mut v___f_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    v___f_1486_ = l_Lake_instInhabitedLeanExeConfig_default___closed__0;
    v___x_1487_ = l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__0;
    v___x_1488_ = l_Lake_LeanExeConfig_toLeanConfig___proj___lam__3___closed__1;
    v___x_1489_ = l_Lake_instInhabitedLeanExeConfig_default___closed__1;
    v___x_1490_ = l_Lake_instInhabitedLeanExeConfig_default___closed__2;
    v___x_1491_ = 0;
    v___f_1492_ = l_Lake_LeanExeConfig_instEmptyCollection___closed__0;
    lean_inc(v_name_1485_);
    v___x_1493_ = l_Lean_Name_toStringWithSep(v___x_1490_, v___x_1491_, v_name_1485_, v___f_1492_);
    v___x_1494_ = lean_alloc_ctor(0, 7, (1) as u32);
    lean_ctor_set(v___x_1494_, 0, v___x_1488_);
    lean_ctor_set(v___x_1494_, 1, v___x_1489_);
    lean_ctor_set(v___x_1494_, 2, v_name_1485_);
    lean_ctor_set(v___x_1494_, 3, v___x_1493_);
    lean_ctor_set(v___x_1494_, 4, v___x_1487_);
    lean_ctor_set(v___x_1494_, 5, v___x_1487_);
    lean_ctor_set(v___x_1494_, 6, v___f_1486_);
    lean_ctor_set_uint8(
        v___x_1494_,
        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
        v___x_1491_,
    );
    return v___x_1494_;
}
pub unsafe fn l_Lake_LeanExeConfig_name___redArg(
    mut v_n_1495_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_n_1495_);
    return v_n_1495_;
}
pub unsafe fn l_Lake_LeanExeConfig_name___redArg___boxed(
    mut v_n_1496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1497_: *mut LeanObject = core::ptr::null_mut();
    v_res_1497_ = l_Lake_LeanExeConfig_name___redArg(v_n_1496_);
    lean_dec(v_n_1496_);
    return v_res_1497_;
}
pub unsafe fn l_Lake_LeanExeConfig_name(
    mut v_n_1498_: *mut LeanObject,
    mut v_x_1499_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_n_1498_);
    return v_n_1498_;
}
pub unsafe fn l_Lake_LeanExeConfig_name___boxed(
    mut v_n_1500_: *mut LeanObject,
    mut v_x_1501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1502_: *mut LeanObject = core::ptr::null_mut();
    v_res_1502_ = l_Lake_LeanExeConfig_name(v_n_1500_, v_x_1501_);
    lean_dec_ref(v_x_1501_);
    lean_dec(v_n_1500_);
    return v_res_1502_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_LeanExeConfig(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Facets(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_LeanExeConfig___fields = _init_l_Lake_LeanExeConfig___fields();
    lean_mark_persistent(l_Lake_LeanExeConfig___fields);
    l_Lake_LeanExeConfig_instConfigInfo = _init_l_Lake_LeanExeConfig_instConfigInfo();
    lean_mark_persistent(l_Lake_LeanExeConfig_instConfigInfo);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_LeanExeConfig(builtin: u8) -> *mut LeanObject {
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
pub unsafe fn initialize_Lake_Config_LeanExeConfig(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Facets(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_LeanConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanExeConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Config_LeanExeConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Config_LeanExeConfig(builtin);
}
