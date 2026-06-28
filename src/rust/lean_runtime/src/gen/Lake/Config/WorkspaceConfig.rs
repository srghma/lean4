// Lean compiler output
// Module: Lake.Config.WorkspaceConfig
// Imports: Lake.Config.Defaults Lake.Config.MetaClasses Lake.Config.Meta Lake.Config.Meta
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::Repr::{l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Lake::Config::Defaults::{
    initialize_Lake_Config_Defaults, l_Lake_defaultPackagesDir,
    runtime_initialize_Lake_Config_Defaults,
};
use crate::r#gen::Lake::Config::Meta::{
    initialize_Lake_Config_Meta, meta_initialize_Lake_Config_Meta,
    runtime_initialize_Lake_Config_Meta,
};
use crate::r#gen::Lake::Config::MetaClasses::{
    initialize_Lake_Config_MetaClasses, runtime_initialize_Lake_Config_MetaClasses,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_usize_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
    lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_box, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once,
    lean_uint8_once, lean_unsigned_to_nat, lean_usize_once,
};
pub static mut l_Lake_instInhabitedWorkspaceConfig_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_instInhabitedWorkspaceConfig: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_instReprWorkspaceConfig_repr___redArg___closed__0_value: LeanStringObject<3> =
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
static mut l_Lake_instReprWorkspaceConfig_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instReprWorkspaceConfig_repr___redArg___closed__1_value: LeanStringObject<12> =
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
        m_data: [112, 97, 99, 107, 97, 103, 101, 115, 68, 105, 114, 0],
    };
static mut l_Lake_instReprWorkspaceConfig_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_instReprWorkspaceConfig_repr___redArg___closed__2_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprWorkspaceConfig_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_instReprWorkspaceConfig_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprWorkspaceConfig_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_instReprWorkspaceConfig_repr___redArg___closed__4_value: LeanStringObject<5> =
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
static mut l_Lake_instReprWorkspaceConfig_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lake_instReprWorkspaceConfig_repr___redArg___closed__5_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprWorkspaceConfig_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lake_instReprWorkspaceConfig_repr___redArg___closed__6_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprWorkspaceConfig_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lake_instReprWorkspaceConfig_repr___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprWorkspaceConfig_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprWorkspaceConfig_repr___redArg___closed__8_value: LeanStringObject<13> =
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
        m_data: [70, 105, 108, 101, 80, 97, 116, 104, 46, 109, 107, 32, 0],
    };
static mut l_Lake_instReprWorkspaceConfig_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lake_instReprWorkspaceConfig_repr___redArg___closed__9_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprWorkspaceConfig_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lake_instReprWorkspaceConfig_repr___redArg___closed__10_value: LeanStringObject<3> =
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
static mut l_Lake_instReprWorkspaceConfig_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__10_value)
        as *mut LeanObject;
static mut l_Lake_instReprWorkspaceConfig_repr___redArg___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprWorkspaceConfig_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprWorkspaceConfig_repr___redArg___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprWorkspaceConfig_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprWorkspaceConfig_repr___redArg___closed__13_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprWorkspaceConfig_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Lake_instReprWorkspaceConfig_repr___redArg___closed__14_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lake_instReprWorkspaceConfig_repr___redArg___closed__10_value
        ) as *mut LeanObject],
    };
static mut l_Lake_instReprWorkspaceConfig_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__14_value)
        as *mut LeanObject;
pub static l_Lake_instReprWorkspaceConfig___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instReprWorkspaceConfig_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprWorkspaceConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprWorkspaceConfig___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprWorkspaceConfig: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprWorkspaceConfig___closed__0_value) as *mut LeanObject;
pub static l_Lake_WorkspaceConfig_packagesDir___proj___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_WorkspaceConfig_packagesDir___proj___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_WorkspaceConfig_packagesDir___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_WorkspaceConfig_packagesDir___proj___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_WorkspaceConfig_packagesDir___proj___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_WorkspaceConfig_packagesDir___proj___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_WorkspaceConfig_packagesDir___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_WorkspaceConfig_packagesDir___proj___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_WorkspaceConfig_packagesDir___proj___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_WorkspaceConfig_packagesDir___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_WorkspaceConfig_packagesDir___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_WorkspaceConfig_packagesDir___proj___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_WorkspaceConfig_packagesDir___proj___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_WorkspaceConfig_packagesDir___proj___lam__3___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_WorkspaceConfig_packagesDir___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_WorkspaceConfig_packagesDir___proj___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_WorkspaceConfig_packagesDir___proj___closed__4_value: LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Lake_WorkspaceConfig_packagesDir___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_WorkspaceConfig_packagesDir___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_WorkspaceConfig_packagesDir___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_WorkspaceConfig_packagesDir___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_WorkspaceConfig_packagesDir___proj___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_WorkspaceConfig_packagesDir___proj___closed__4_value)
        as *mut LeanObject;
pub static mut l_Lake_WorkspaceConfig_packagesDir___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_WorkspaceConfig_packagesDir___proj___closed__4_value)
        as *mut LeanObject;
pub static mut l_Lake_WorkspaceConfig_packagesDir_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_WorkspaceConfig_packagesDir___proj___closed__4_value)
        as *mut LeanObject;
pub static l_Lake_WorkspaceConfig___fields___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lake_WorkspaceConfig___fields___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_WorkspaceConfig___fields___closed__0_value) as *mut LeanObject;
pub static l_Lake_WorkspaceConfig___fields___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__1_value)
            as *mut LeanObject,
        795032257962021837 as *mut LeanObject,
    ],
};
static mut l_Lake_WorkspaceConfig___fields___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_WorkspaceConfig___fields___closed__1_value) as *mut LeanObject;
pub static l_Lake_WorkspaceConfig___fields___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_WorkspaceConfig___fields___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_WorkspaceConfig___fields___closed__1_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_WorkspaceConfig___fields___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_WorkspaceConfig___fields___closed__2_value) as *mut LeanObject;
static mut l_Lake_WorkspaceConfig___fields___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_WorkspaceConfig___fields___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_WorkspaceConfig___fields: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_WorkspaceConfig_instConfigFields: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_WorkspaceConfig_instConfigInfo___closed__1_value: LeanClosureObject<0> =
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
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_WorkspaceConfig_instConfigInfo___closed__1_value) as *mut LeanObject;
pub static l_Lake_WorkspaceConfig_instConfigInfo___closed__2_value: LeanClosureObject<0> =
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
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_WorkspaceConfig_instConfigInfo___closed__2_value) as *mut LeanObject;
pub static l_Lake_WorkspaceConfig_instConfigInfo___closed__3_value: LeanClosureObject<0> =
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
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_WorkspaceConfig_instConfigInfo___closed__3_value) as *mut LeanObject;
pub static l_Lake_WorkspaceConfig_instConfigInfo___closed__4_value: LeanClosureObject<0> =
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
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_WorkspaceConfig_instConfigInfo___closed__4_value) as *mut LeanObject;
pub static l_Lake_WorkspaceConfig_instConfigInfo___closed__5_value: LeanClosureObject<0> =
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
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_WorkspaceConfig_instConfigInfo___closed__5_value) as *mut LeanObject;
pub static l_Lake_WorkspaceConfig_instConfigInfo___closed__6_value: LeanClosureObject<0> =
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
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_WorkspaceConfig_instConfigInfo___closed__6_value) as *mut LeanObject;
pub static l_Lake_WorkspaceConfig_instConfigInfo___closed__7_value: LeanClosureObject<0> =
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
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_WorkspaceConfig_instConfigInfo___closed__7_value) as *mut LeanObject;
pub static l_Lake_WorkspaceConfig_instConfigInfo___closed__8_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_WorkspaceConfig_instConfigInfo___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_WorkspaceConfig_instConfigInfo___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_WorkspaceConfig_instConfigInfo___closed__8_value) as *mut LeanObject;
pub static l_Lake_WorkspaceConfig_instConfigInfo___closed__9_value: LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Lake_WorkspaceConfig_instConfigInfo___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_WorkspaceConfig_instConfigInfo___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_WorkspaceConfig_instConfigInfo___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_WorkspaceConfig_instConfigInfo___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_WorkspaceConfig_instConfigInfo___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_WorkspaceConfig_instConfigInfo___closed__9_value) as *mut LeanObject;
pub static l_Lake_WorkspaceConfig_instConfigInfo___closed__10_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_WorkspaceConfig_instConfigInfo___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_WorkspaceConfig_instConfigInfo___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_WorkspaceConfig_instConfigInfo___closed__10_value)
        as *mut LeanObject;
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__11: u8 = 0;
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_WorkspaceConfig_instConfigInfo___closed__13_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_WorkspaceConfig_instConfigInfo___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_WorkspaceConfig_instConfigInfo___closed__13_value)
        as *mut LeanObject;
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__14: u8 = 0;
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__15: usize = 0;
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_WorkspaceConfig_instConfigInfo___closed__17: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_WorkspaceConfig_instConfigInfo: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_WorkspaceConfig_instEmptyCollection: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lake_instInhabitedWorkspaceConfig_default() -> *mut LeanObject {
    let mut v___x_154_: *mut LeanObject = core::ptr::null_mut();
    v___x_154_ = l_Lake_defaultPackagesDir;
    return v___x_154_;
}
pub unsafe fn _init_l_Lake_instInhabitedWorkspaceConfig() -> *mut LeanObject {
    let mut v___x_155_: *mut LeanObject = core::ptr::null_mut();
    v___x_155_ = l_Lake_defaultPackagesDir;
    return v___x_155_;
}
pub unsafe fn l_Nat_cast___at___00Lake_instReprWorkspaceConfig_repr_spec__0(
    mut v_a_156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_157_: *mut LeanObject = core::ptr::null_mut();
    v___x_157_ = lean_nat_to_int(v_a_156_);
    return v___x_157_;
}
pub unsafe fn _init_l_Lake_instReprWorkspaceConfig_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_172_: *mut LeanObject = core::ptr::null_mut();
    v___x_171_ = lean_unsigned_to_nat(15);
    v___x_172_ = lean_nat_to_int(v___x_171_);
    return v___x_172_;
}
pub unsafe fn _init_l_Lake_instReprWorkspaceConfig_repr___redArg___closed__11() -> *mut LeanObject {
    let mut v___x_177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_178_: *mut LeanObject = core::ptr::null_mut();
    v___x_177_ = l_Lake_instReprWorkspaceConfig_repr___redArg___closed__0;
    v___x_178_ = lean_string_length(v___x_177_);
    return v___x_178_;
}
pub unsafe fn _init_l_Lake_instReprWorkspaceConfig_repr___redArg___closed__12() -> *mut LeanObject {
    let mut v___x_179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut LeanObject = core::ptr::null_mut();
    v___x_179_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__11),
        core::ptr::addr_of_mut!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__11_once),
        _init_l_Lake_instReprWorkspaceConfig_repr___redArg___closed__11,
    );
    v___x_180_ = lean_nat_to_int(v___x_179_);
    return v___x_180_;
}
pub unsafe fn l_Lake_instReprWorkspaceConfig_repr___redArg(
    mut v_x_185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_195_: u8 = 0;
    let mut v___x_196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
    v___x_186_ = l_Lake_instReprWorkspaceConfig_repr___redArg___closed__6;
    v___x_187_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__7_once),
        _init_l_Lake_instReprWorkspaceConfig_repr___redArg___closed__7,
    );
    v___x_188_ = lean_unsigned_to_nat(0);
    v___x_189_ = l_Lake_instReprWorkspaceConfig_repr___redArg___closed__9;
    v___x_190_ = l_String_quote(v_x_185_);
    v___x_191_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_191_, 0, v___x_190_);
    v___x_192_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_192_, 0, v___x_189_);
    lean_ctor_set(v___x_192_, 1, v___x_191_);
    v___x_193_ = l_Repr_addAppParen(v___x_192_, v___x_188_);
    v___x_194_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_194_, 0, v___x_187_);
    lean_ctor_set(v___x_194_, 1, v___x_193_);
    v___x_195_ = 0;
    v___x_196_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_196_, 0, v___x_194_);
    lean_ctor_set_uint8(
        v___x_196_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_195_,
    );
    v___x_197_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_197_, 0, v___x_186_);
    lean_ctor_set(v___x_197_, 1, v___x_196_);
    v___x_198_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lake_instReprWorkspaceConfig_repr___redArg___closed__12_once),
        _init_l_Lake_instReprWorkspaceConfig_repr___redArg___closed__12,
    );
    v___x_199_ = l_Lake_instReprWorkspaceConfig_repr___redArg___closed__13;
    v___x_200_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_200_, 0, v___x_199_);
    lean_ctor_set(v___x_200_, 1, v___x_197_);
    v___x_201_ = l_Lake_instReprWorkspaceConfig_repr___redArg___closed__14;
    v___x_202_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_202_, 0, v___x_200_);
    lean_ctor_set(v___x_202_, 1, v___x_201_);
    v___x_203_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_203_, 0, v___x_198_);
    lean_ctor_set(v___x_203_, 1, v___x_202_);
    v___x_204_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_204_, 0, v___x_203_);
    lean_ctor_set_uint8(
        v___x_204_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_195_,
    );
    return v___x_204_;
}
pub unsafe fn l_Lake_instReprWorkspaceConfig_repr(
    mut v_x_205_: *mut LeanObject,
    mut v_prec_206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
    v___x_207_ = l_Lake_instReprWorkspaceConfig_repr___redArg(v_x_205_);
    return v___x_207_;
}
pub unsafe fn l_Lake_instReprWorkspaceConfig_repr___boxed(
    mut v_x_208_: *mut LeanObject,
    mut v_prec_209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_210_: *mut LeanObject = core::ptr::null_mut();
    v_res_210_ = l_Lake_instReprWorkspaceConfig_repr(v_x_208_, v_prec_209_);
    lean_dec(v_prec_209_);
    return v_res_210_;
}
pub unsafe fn l_Lake_WorkspaceConfig_packagesDir___proj___lam__0(
    mut v_cfg_213_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_cfg_213_);
    return v_cfg_213_;
}
pub unsafe fn l_Lake_WorkspaceConfig_packagesDir___proj___lam__0___boxed(
    mut v_cfg_214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_215_: *mut LeanObject = core::ptr::null_mut();
    v_res_215_ = l_Lake_WorkspaceConfig_packagesDir___proj___lam__0(v_cfg_214_);
    lean_dec_ref(v_cfg_214_);
    return v_res_215_;
}
pub unsafe fn l_Lake_WorkspaceConfig_packagesDir___proj___lam__1(
    mut v_val_216_: *mut LeanObject,
    mut v_cfg_217_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_val_216_);
    return v_val_216_;
}
pub unsafe fn l_Lake_WorkspaceConfig_packagesDir___proj___lam__1___boxed(
    mut v_val_218_: *mut LeanObject,
    mut v_cfg_219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_220_: *mut LeanObject = core::ptr::null_mut();
    v_res_220_ = l_Lake_WorkspaceConfig_packagesDir___proj___lam__1(v_val_218_, v_cfg_219_);
    lean_dec_ref(v_cfg_219_);
    lean_dec_ref(v_val_218_);
    return v_res_220_;
}
pub unsafe fn l_Lake_WorkspaceConfig_packagesDir___proj___lam__2(
    mut v_f_221_: *mut LeanObject,
    mut v_cfg_222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
    v___x_223_ = lean_apply_1(v_f_221_, v_cfg_222_);
    return v___x_223_;
}
pub unsafe fn l_Lake_WorkspaceConfig_packagesDir___proj___lam__3(
    mut v_x_224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
    v___x_225_ = l_Lake_defaultPackagesDir;
    return v___x_225_;
}
pub unsafe fn l_Lake_WorkspaceConfig_packagesDir___proj___lam__3___boxed(
    mut v_x_226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_227_: *mut LeanObject = core::ptr::null_mut();
    v_res_227_ = l_Lake_WorkspaceConfig_packagesDir___proj___lam__3(v_x_226_);
    lean_dec_ref(v_x_226_);
    return v_res_227_;
}
pub unsafe fn _init_l_Lake_WorkspaceConfig___fields___closed__3() -> *mut LeanObject {
    let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut LeanObject = core::ptr::null_mut();
    v___x_247_ = l_Lake_WorkspaceConfig___fields___closed__2;
    v___x_248_ = l_Lake_WorkspaceConfig___fields___closed__0;
    v___x_249_ = lean_array_push(v___x_248_, v___x_247_);
    return v___x_249_;
}
pub unsafe fn _init_l_Lake_WorkspaceConfig___fields() -> *mut LeanObject {
    let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
    v___x_250_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_WorkspaceConfig___fields___closed__3),
        core::ptr::addr_of_mut!(l_Lake_WorkspaceConfig___fields___closed__3_once),
        _init_l_Lake_WorkspaceConfig___fields___closed__3,
    );
    return v___x_250_;
}
pub unsafe fn _init_l_Lake_WorkspaceConfig_instConfigFields() -> *mut LeanObject {
    let mut v___x_251_: *mut LeanObject = core::ptr::null_mut();
    v___x_251_ = l_Lake_WorkspaceConfig___fields;
    return v___x_251_;
}
pub unsafe fn l_Lake_WorkspaceConfig_instConfigInfo___lam__0(
    mut v_x1_252_: *mut LeanObject,
    mut v_x2_253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut LeanObject = core::ptr::null_mut();
    v_name_254_ = lean_ctor_get(v_x2_253_, 0);
    lean_inc(v_name_254_);
    v___x_255_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_name_254_,
        v_x2_253_,
        v_x1_252_,
    );
    return v___x_255_;
}
pub unsafe fn _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__0() -> *mut LeanObject {
    let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut LeanObject = core::ptr::null_mut();
    v___x_256_ = l_Lake_WorkspaceConfig___fields;
    v___x_257_ = lean_array_get_size(v___x_256_);
    return v___x_257_;
}
pub unsafe fn _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__11() -> u8 {
    let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_279_: u8 = 0;
    v___x_277_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_WorkspaceConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_WorkspaceConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__0,
    );
    v___x_278_ = lean_unsigned_to_nat(0);
    v___x_279_ = lean_nat_dec_lt(v___x_278_, v___x_277_);
    return v___x_279_;
}
pub unsafe fn _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__12() -> *mut LeanObject {
    let mut v___x_280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut LeanObject = core::ptr::null_mut();
    v___x_280_ = lean_unsigned_to_nat(0);
    v___x_281_ = lean_box(1);
    v___x_282_ = l_Lake_WorkspaceConfig___fields;
    v___x_283_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_283_, 0, v___x_282_);
    lean_ctor_set(v___x_283_, 1, v___x_281_);
    lean_ctor_set(v___x_283_, 2, v___x_280_);
    return v___x_283_;
}
pub unsafe fn _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__14() -> u8 {
    let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_286_: u8 = 0;
    v___x_285_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_WorkspaceConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_WorkspaceConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__0,
    );
    v___x_286_ = lean_nat_dec_le(v___x_285_, v___x_285_);
    return v___x_286_;
}
pub unsafe fn _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__15() -> usize {
    let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_288_: usize = 0;
    v___x_287_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_WorkspaceConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_WorkspaceConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__0,
    );
    v___x_288_ = lean_usize_of_nat(v___x_287_);
    return v___x_288_;
}
pub unsafe fn _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__16() -> *mut LeanObject {
    let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_290_: usize = 0;
    let mut v___x_291_: usize = 0;
    let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut LeanObject = core::ptr::null_mut();
    v___x_289_ = lean_box(1);
    v___x_290_ = lean_usize_once(
        core::ptr::addr_of_mut!(l_Lake_WorkspaceConfig_instConfigInfo___closed__15),
        core::ptr::addr_of_mut!(l_Lake_WorkspaceConfig_instConfigInfo___closed__15_once),
        _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__15,
    );
    v___x_291_ = 0usize;
    v___x_292_ = l_Lake_WorkspaceConfig___fields;
    v___f_293_ = l_Lake_WorkspaceConfig_instConfigInfo___closed__13;
    v___x_294_ = l_Lake_WorkspaceConfig_instConfigInfo___closed__10;
    v___x_295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_294_,
        v___f_293_,
        v___x_292_,
        v___x_291_,
        v___x_290_,
        v___x_289_,
    );
    return v___x_295_;
}
pub unsafe fn _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__17() -> *mut LeanObject {
    let mut v___x_296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut LeanObject = core::ptr::null_mut();
    v___x_296_ = lean_unsigned_to_nat(0);
    v___x_297_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_WorkspaceConfig_instConfigInfo___closed__16),
        core::ptr::addr_of_mut!(l_Lake_WorkspaceConfig_instConfigInfo___closed__16_once),
        _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__16,
    );
    v___x_298_ = l_Lake_WorkspaceConfig___fields;
    v___x_299_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_299_, 0, v___x_298_);
    lean_ctor_set(v___x_299_, 1, v___x_297_);
    lean_ctor_set(v___x_299_, 2, v___x_296_);
    return v___x_299_;
}
pub unsafe fn _init_l_Lake_WorkspaceConfig_instConfigInfo() -> *mut LeanObject {
    let mut v___x_300_: u8 = 0;
    v___x_300_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_Lake_WorkspaceConfig_instConfigInfo___closed__11),
        core::ptr::addr_of_mut!(l_Lake_WorkspaceConfig_instConfigInfo___closed__11_once),
        _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__11,
    );
    if v___x_300_ == 0 {
        let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
        v___x_301_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lake_WorkspaceConfig_instConfigInfo___closed__12),
            core::ptr::addr_of_mut!(l_Lake_WorkspaceConfig_instConfigInfo___closed__12_once),
            _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__12,
        );
        return v___x_301_;
    } else {
        let mut v___x_302_: u8 = 0;
        v___x_302_ = lean_uint8_once(
            core::ptr::addr_of_mut!(l_Lake_WorkspaceConfig_instConfigInfo___closed__14),
            core::ptr::addr_of_mut!(l_Lake_WorkspaceConfig_instConfigInfo___closed__14_once),
            _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__14,
        );
        if v___x_302_ == 0 {
            if v___x_300_ == 0 {
                let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
                v___x_303_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_WorkspaceConfig_instConfigInfo___closed__12),
                    core::ptr::addr_of_mut!(
                        l_Lake_WorkspaceConfig_instConfigInfo___closed__12_once
                    ),
                    _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__12,
                );
                return v___x_303_;
            } else {
                let mut v___x_304_: *mut LeanObject = core::ptr::null_mut();
                v___x_304_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_WorkspaceConfig_instConfigInfo___closed__17),
                    core::ptr::addr_of_mut!(
                        l_Lake_WorkspaceConfig_instConfigInfo___closed__17_once
                    ),
                    _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__17,
                );
                return v___x_304_;
            }
        } else {
            let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
            v___x_305_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lake_WorkspaceConfig_instConfigInfo___closed__17),
                core::ptr::addr_of_mut!(l_Lake_WorkspaceConfig_instConfigInfo___closed__17_once),
                _init_l_Lake_WorkspaceConfig_instConfigInfo___closed__17,
            );
            return v___x_305_;
        }
    }
}
pub unsafe fn _init_l_Lake_WorkspaceConfig_instEmptyCollection() -> *mut LeanObject {
    let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
    v___x_306_ = l_Lake_defaultPackagesDir;
    return v___x_306_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_WorkspaceConfig(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Defaults(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_MetaClasses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_instInhabitedWorkspaceConfig_default =
        _init_l_Lake_instInhabitedWorkspaceConfig_default();
    lean_mark_persistent(l_Lake_instInhabitedWorkspaceConfig_default);
    l_Lake_instInhabitedWorkspaceConfig = _init_l_Lake_instInhabitedWorkspaceConfig();
    lean_mark_persistent(l_Lake_instInhabitedWorkspaceConfig);
    l_Lake_WorkspaceConfig___fields = _init_l_Lake_WorkspaceConfig___fields();
    lean_mark_persistent(l_Lake_WorkspaceConfig___fields);
    l_Lake_WorkspaceConfig_instConfigFields = _init_l_Lake_WorkspaceConfig_instConfigFields();
    lean_mark_persistent(l_Lake_WorkspaceConfig_instConfigFields);
    l_Lake_WorkspaceConfig_instConfigInfo = _init_l_Lake_WorkspaceConfig_instConfigInfo();
    lean_mark_persistent(l_Lake_WorkspaceConfig_instConfigInfo);
    l_Lake_WorkspaceConfig_instEmptyCollection = _init_l_Lake_WorkspaceConfig_instEmptyCollection();
    lean_mark_persistent(l_Lake_WorkspaceConfig_instEmptyCollection);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_WorkspaceConfig(builtin: u8) -> *mut LeanObject {
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
pub unsafe fn initialize_Lake_Config_WorkspaceConfig(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Defaults(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_MetaClasses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_WorkspaceConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Config_WorkspaceConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Config_WorkspaceConfig(builtin);
}
