// Lean compiler output
// Module: Lake.Config.InputFileConfig
// Imports: Lake.Config.Pattern Lake.Config.MetaClasses Init.Data.ToString.Name Lake.Config.Meta Lake.Config.Meta
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::ToString::Name::{
    initialize_Init_Data_ToString_Name, l_Lean_Name_toString,
    runtime_initialize_Init_Data_ToString_Name,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Lake::Config::Meta::{
    initialize_Lake_Config_Meta, runtime_initialize_Lake_Config_Meta,
};
use crate::r#gen::Lake::Config::MetaClasses::{
    initialize_Lake_Config_MetaClasses, runtime_initialize_Lake_Config_MetaClasses,
};
use crate::r#gen::Lake::Config::Pattern::{
    initialize_Lake_Config_Pattern, l_Lake_Pattern_star, runtime_initialize_Lake_Config_Pattern,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_usize_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
    lean_nat_dec_lt,
};
pub static l_Lake_InputFileConfig_path___proj___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_InputFileConfig_path___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_InputFileConfig_path___proj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_path___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFileConfig_path___proj___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_InputFileConfig_path___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_InputFileConfig_path___proj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_path___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFileConfig_path___proj___closed__2_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_InputFileConfig_path___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_InputFileConfig_path___proj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_path___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFileConfig_text___proj___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_InputFileConfig_text___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_InputFileConfig_text___proj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_text___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFileConfig_text___proj___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_InputFileConfig_text___proj___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_InputFileConfig_text___proj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_text___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFileConfig_text___proj___closed__2_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_InputFileConfig_text___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_InputFileConfig_text___proj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_text___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFileConfig_text___proj___closed__3_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_InputFileConfig_text___proj___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_InputFileConfig_text___proj___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_text___proj___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFileConfig_text___proj___closed__4_value: crate::leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Lake_InputFileConfig_text___proj___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_InputFileConfig_text___proj___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_InputFileConfig_text___proj___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_InputFileConfig_text___proj___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_InputFileConfig_text___proj___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_text___proj___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFileConfig___fields___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lake_InputFileConfig___fields___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFileConfig___fields___closed__1_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [112, 97, 116, 104, 0],
    };
static mut l_Lake_InputFileConfig___fields___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFileConfig___fields___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__1_value)
                as *mut crate::leanh::LeanObject,
            1599759234323164429 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_InputFileConfig___fields___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFileConfig___fields___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__2_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_InputFileConfig___fields___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_InputFileConfig___fields___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_InputFileConfig___fields___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_InputFileConfig___fields___closed__5_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [116, 101, 120, 116, 0],
    };
static mut l_Lake_InputFileConfig___fields___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFileConfig___fields___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__5_value)
                as *mut crate::leanh::LeanObject,
            11956103831239991322 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_InputFileConfig___fields___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFileConfig___fields___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__6_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_InputFileConfig___fields___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_InputFileConfig___fields___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_InputFileConfig___fields___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_InputFileConfig___fields: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_InputFileConfig_instConfigInfo___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_InputFileConfig_instConfigInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_InputFileConfig_instConfigInfo___closed__1_value:
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
static mut l_Lake_InputFileConfig_instConfigInfo___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFileConfig_instConfigInfo___closed__2_value:
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
static mut l_Lake_InputFileConfig_instConfigInfo___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFileConfig_instConfigInfo___closed__3_value:
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
static mut l_Lake_InputFileConfig_instConfigInfo___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFileConfig_instConfigInfo___closed__4_value:
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
static mut l_Lake_InputFileConfig_instConfigInfo___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFileConfig_instConfigInfo___closed__5_value:
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
static mut l_Lake_InputFileConfig_instConfigInfo___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFileConfig_instConfigInfo___closed__6_value:
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
static mut l_Lake_InputFileConfig_instConfigInfo___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFileConfig_instConfigInfo___closed__7_value:
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
static mut l_Lake_InputFileConfig_instConfigInfo___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFileConfig_instConfigInfo___closed__8_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_InputFileConfig_instConfigInfo___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFileConfig_instConfigInfo___closed__9_value: crate::leanh::LeanCtorObject<
    5,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__5_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_InputFileConfig_instConfigInfo___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputFileConfig_instConfigInfo___closed__10_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_InputFileConfig_instConfigInfo___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_InputFileConfig_instConfigInfo___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_InputFileConfig_instConfigInfo___closed__11: u8 = 0;
pub static l_Lake_InputFileConfig_instConfigInfo___closed__12_value:
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
    m_fun: l_Lake_InputFileConfig_instConfigInfo___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_InputFileConfig_instConfigInfo___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_InputFileConfig_instConfigInfo___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_InputFileConfig_instConfigInfo___closed__13: u8 = 0;
static mut l_Lake_InputFileConfig_instConfigInfo___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_InputFileConfig_instConfigInfo___closed__14: usize = 0;
static mut l_Lake_InputFileConfig_instConfigInfo___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_InputFileConfig_instConfigInfo___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_InputFileConfig_instConfigInfo: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_InputDirConfig_path___proj___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_InputDirConfig_path___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputDirConfig_path___proj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_path___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputDirConfig_path___proj___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_InputDirConfig_path___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputDirConfig_path___proj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_path___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputDirConfig_path___proj___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_InputDirConfig_path___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputDirConfig_path___proj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_path___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputDirConfig_text___proj___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_InputDirConfig_text___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputDirConfig_text___proj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_text___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputDirConfig_text___proj___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_InputDirConfig_text___proj___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputDirConfig_text___proj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_text___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputDirConfig_text___proj___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_InputDirConfig_text___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputDirConfig_text___proj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_text___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputDirConfig_text___proj___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_InputDirConfig_text___proj___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputDirConfig_text___proj___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_text___proj___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputDirConfig_text___proj___closed__4_value: crate::leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Lake_InputDirConfig_text___proj___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_InputDirConfig_text___proj___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_InputDirConfig_text___proj___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_InputDirConfig_text___proj___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_InputDirConfig_text___proj___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_text___proj___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_InputDirConfig_filter___proj___lam__3___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_InputDirConfig_filter___proj___lam__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_InputDirConfig_filter___proj___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_InputDirConfig_filter___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_InputDirConfig_filter___proj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_filter___proj___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputDirConfig_filter___proj___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_InputDirConfig_filter___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_InputDirConfig_filter___proj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_filter___proj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputDirConfig_filter___proj___closed__2_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_InputDirConfig_filter___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_InputDirConfig_filter___proj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_filter___proj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputDirConfig_filter___proj___closed__3_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lake_InputDirConfig_filter___proj___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_InputDirConfig_filter___proj___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_filter___proj___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputDirConfig_filter___proj___closed__4_value: crate::leanh::LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Lake_InputDirConfig_filter___proj___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_InputDirConfig_filter___proj___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_InputDirConfig_filter___proj___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_InputDirConfig_filter___proj___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_InputDirConfig_filter___proj___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_filter___proj___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputDirConfig___fields___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [102, 105, 108, 116, 101, 114, 0],
    };
static mut l_Lake_InputDirConfig___fields___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig___fields___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputDirConfig___fields___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_InputDirConfig___fields___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11672201034198194596 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_InputDirConfig___fields___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig___fields___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InputDirConfig___fields___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_InputDirConfig___fields___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_InputDirConfig___fields___closed__1_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_InputDirConfig___fields___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig___fields___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_InputDirConfig___fields___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_InputDirConfig___fields___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_InputDirConfig___fields: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_InputDirConfig_instConfigInfo___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_InputDirConfig_instConfigInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_InputDirConfig_instConfigInfo___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_InputDirConfig_instConfigInfo___closed__1: u8 = 0;
static mut l_Lake_InputDirConfig_instConfigInfo___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_InputDirConfig_instConfigInfo___closed__2: u8 = 0;
static mut l_Lake_InputDirConfig_instConfigInfo___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_InputDirConfig_instConfigInfo___closed__3: usize = 0;
static mut l_Lake_InputDirConfig_instConfigInfo___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_InputDirConfig_instConfigInfo___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_InputDirConfig_instConfigInfo: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lake_InputFileConfig_path___proj___lam__0(
    mut v_cfg_383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_path_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_path_384_ = crate::leanh::lean_ctor_get(v_cfg_383_, 0);
    crate::leanh::lean_inc_ref(v_path_384_);
    return v_path_384_;
}
pub unsafe fn l_Lake_InputFileConfig_path___proj___lam__0___boxed(
    mut v_cfg_385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_386_ = l_Lake_InputFileConfig_path___proj___lam__0(v_cfg_385_);
    crate::leanh::lean_dec_ref(v_cfg_385_);
    return v_res_386_;
}
pub unsafe fn l_Lake_InputFileConfig_path___proj___lam__1(
    mut v_val_387_: *mut crate::leanh::LeanObject,
    mut v_cfg_388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_text_389_: u8 = 0;
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_392_: u8 = 0;
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_396_: u8 = 0;
    let mut v_unused_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_text_389_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_388_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_396_ = (!crate::leanh::lean_is_exclusive(v_cfg_388_)) as u8;
                if v_isSharedCheck_396_ == 0 {
                    v_unused_397_ = crate::leanh::lean_ctor_get(v_cfg_388_, 0);
                    crate::leanh::lean_dec(v_unused_397_);
                    v___x_391_ = v_cfg_388_;
                    v_isShared_392_ = v_isSharedCheck_396_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_cfg_388_);
                    v___x_391_ = crate::leanh::lean_box(0);
                    v_isShared_392_ = v_isSharedCheck_396_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_392_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_391_, 0, v_val_387_);
                    v___x_394_ = v___x_391_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_395_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_395_, 0, v_val_387_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_395_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_text_389_,
                    );
                    v___x_394_ = v_reuseFailAlloc_395_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_394_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputFileConfig_path___proj___lam__2(
    mut v_f_398_: *mut crate::leanh::LeanObject,
    mut v_cfg_399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_path_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_401_: u8 = 0;
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_404_: u8 = 0;
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_409_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_path_400_ = crate::leanh::lean_ctor_get(v_cfg_399_, 0);
                v_text_401_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_399_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_409_ = (!crate::leanh::lean_is_exclusive(v_cfg_399_)) as u8;
                if v_isSharedCheck_409_ == 0 {
                    v___x_403_ = v_cfg_399_;
                    v_isShared_404_ = v_isSharedCheck_409_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_path_400_);
                    crate::leanh::lean_dec(v_cfg_399_);
                    v___x_403_ = crate::leanh::lean_box(0);
                    v_isShared_404_ = v_isSharedCheck_409_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_405_ = crate::leanh::lean_apply_1(v_f_398_, v_path_400_);
                if v_isShared_404_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_403_, 0, v___x_405_);
                    v___x_407_ = v___x_403_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_408_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_408_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_text_401_,
                    );
                    v___x_407_ = v_reuseFailAlloc_408_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_407_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputFileConfig_path___proj___lam__3(
    mut v_name_410_: *mut crate::leanh::LeanObject,
    mut v_x_411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_412_: u8 = 0;
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_412_ = 0;
    v___x_413_ = l_Lean_Name_toString(v_name_410_, v___x_412_);
    return v___x_413_;
}
pub unsafe fn l_Lake_InputFileConfig_path___proj___lam__3___boxed(
    mut v_name_414_: *mut crate::leanh::LeanObject,
    mut v_x_415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_416_ = l_Lake_InputFileConfig_path___proj___lam__3(v_name_414_, v_x_415_);
    crate::leanh::lean_dec_ref(v_x_415_);
    return v_res_416_;
}
pub unsafe fn l_Lake_InputFileConfig_path___proj(
    mut v_name_420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_421_ = l_Lake_InputFileConfig_path___proj___closed__0;
    v___f_422_ = l_Lake_InputFileConfig_path___proj___closed__1;
    v___f_423_ = l_Lake_InputFileConfig_path___proj___closed__2;
    v___f_424_ = crate::leanh::lean_alloc_closure(
        l_Lake_InputFileConfig_path___proj___lam__3___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_424_, 0, v_name_420_);
    v___x_425_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_425_, 0, v___f_421_);
    crate::leanh::lean_ctor_set(v___x_425_, 1, v___f_422_);
    crate::leanh::lean_ctor_set(v___x_425_, 2, v___f_423_);
    crate::leanh::lean_ctor_set(v___x_425_, 3, v___f_424_);
    return v___x_425_;
}
pub unsafe fn l_Lake_InputFileConfig_path_instConfigField(
    mut v_name_426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_427_ = l_Lake_InputFileConfig_path___proj(v_name_426_);
    return v___x_427_;
}
pub unsafe fn l_Lake_InputFileConfig_text___proj___lam__0(
    mut v_cfg_428_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_text_429_: u8 = 0;
    v_text_429_ = crate::leanh::lean_ctor_get_uint8(
        v_cfg_428_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    return v_text_429_;
}
pub unsafe fn l_Lake_InputFileConfig_text___proj___lam__0___boxed(
    mut v_cfg_430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_431_: u8 = 0;
    let mut v_r_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_431_ = l_Lake_InputFileConfig_text___proj___lam__0(v_cfg_430_);
    crate::leanh::lean_dec_ref(v_cfg_430_);
    v_r_432_ = crate::leanh::lean_box((v_res_431_) as usize);
    return v_r_432_;
}
pub unsafe fn l_Lake_InputFileConfig_text___proj___lam__1(
    mut v_val_433_: u8,
    mut v_cfg_434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_path_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_438_: u8 = 0;
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_442_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_path_435_ = crate::leanh::lean_ctor_get(v_cfg_434_, 0);
                v_isSharedCheck_442_ = (!crate::leanh::lean_is_exclusive(v_cfg_434_)) as u8;
                if v_isSharedCheck_442_ == 0 {
                    v___x_437_ = v_cfg_434_;
                    v_isShared_438_ = v_isSharedCheck_442_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_path_435_);
                    crate::leanh::lean_dec(v_cfg_434_);
                    v___x_437_ = crate::leanh::lean_box(0);
                    v_isShared_438_ = v_isSharedCheck_442_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_438_ == 0 {
                    v___x_440_ = v___x_437_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_441_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_441_, 0, v_path_435_);
                    v___x_440_ = v_reuseFailAlloc_441_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_440_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_val_433_,
                );
                return v___x_440_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputFileConfig_text___proj___lam__1___boxed(
    mut v_val_443_: *mut crate::leanh::LeanObject,
    mut v_cfg_444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_41__boxed_445_: u8 = 0;
    let mut v_res_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_41__boxed_445_ = (crate::leanh::lean_unbox(v_val_443_) as u8);
    v_res_446_ = l_Lake_InputFileConfig_text___proj___lam__1(v_val_41__boxed_445_, v_cfg_444_);
    return v_res_446_;
}
pub unsafe fn l_Lake_InputFileConfig_text___proj___lam__2(
    mut v_f_447_: *mut crate::leanh::LeanObject,
    mut v_cfg_448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_path_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_450_: u8 = 0;
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_453_: u8 = 0;
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: u8 = 0;
    let mut v_reuseFailAlloc_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_460_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_path_449_ = crate::leanh::lean_ctor_get(v_cfg_448_, 0);
                v_text_450_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_448_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_460_ = (!crate::leanh::lean_is_exclusive(v_cfg_448_)) as u8;
                if v_isSharedCheck_460_ == 0 {
                    v___x_452_ = v_cfg_448_;
                    v_isShared_453_ = v_isSharedCheck_460_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_path_449_);
                    crate::leanh::lean_dec(v_cfg_448_);
                    v___x_452_ = crate::leanh::lean_box(0);
                    v_isShared_453_ = v_isSharedCheck_460_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_454_ = crate::leanh::lean_box((v_text_450_) as usize);
                v___x_455_ = crate::leanh::lean_apply_1(v_f_447_, v___x_454_);
                if v_isShared_453_ == 0 {
                    v___x_457_ = v___x_452_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_459_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_459_, 0, v_path_449_);
                    v___x_457_ = v_reuseFailAlloc_459_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_458_ = (crate::leanh::lean_unbox(v___x_455_) as u8);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_457_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_458_,
                );
                return v___x_457_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputFileConfig_text___proj___lam__3(
    mut v_x_461_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_462_: u8 = 0;
    v___x_462_ = 0;
    return v___x_462_;
}
pub unsafe fn l_Lake_InputFileConfig_text___proj___lam__3___boxed(
    mut v_x_463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_464_: u8 = 0;
    let mut v_r_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_464_ = l_Lake_InputFileConfig_text___proj___lam__3(v_x_463_);
    crate::leanh::lean_dec_ref(v_x_463_);
    v_r_465_ = crate::leanh::lean_box((v_res_464_) as usize);
    return v_r_465_;
}
pub unsafe fn l_Lake_InputFileConfig_text___proj(
    mut v_name_475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_476_ = l_Lake_InputFileConfig_text___proj___closed__4;
    return v___x_476_;
}
pub unsafe fn l_Lake_InputFileConfig_text___proj___boxed(
    mut v_name_477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_478_ = l_Lake_InputFileConfig_text___proj(v_name_477_);
    crate::leanh::lean_dec(v_name_477_);
    return v_res_478_;
}
pub unsafe fn l_Lake_InputFileConfig_text_instConfigField(
    mut v_name_479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_480_ = l_Lake_InputFileConfig_text___proj(v_name_479_);
    return v___x_480_;
}
pub unsafe fn l_Lake_InputFileConfig_text_instConfigField___boxed(
    mut v_name_481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_482_ = l_Lake_InputFileConfig_text_instConfigField(v_name_481_);
    crate::leanh::lean_dec(v_name_481_);
    return v_res_482_;
}
pub unsafe fn _init_l_Lake_InputFileConfig___fields___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_492_ = l_Lake_InputFileConfig___fields___closed__3;
    v___x_493_ = l_Lake_InputFileConfig___fields___closed__0;
    v___x_494_ = lean_array_push(v___x_493_, v___x_492_);
    return v___x_494_;
}
pub unsafe fn _init_l_Lake_InputFileConfig___fields___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_502_ = l_Lake_InputFileConfig___fields___closed__7;
    v___x_503_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig___fields___closed__4),
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig___fields___closed__4_once),
        _init_l_Lake_InputFileConfig___fields___closed__4,
    );
    v___x_504_ = lean_array_push(v___x_503_, v___x_502_);
    return v___x_504_;
}
pub unsafe fn _init_l_Lake_InputFileConfig___fields() -> *mut crate::leanh::LeanObject {
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_505_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig___fields___closed__8),
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig___fields___closed__8_once),
        _init_l_Lake_InputFileConfig___fields___closed__8,
    );
    return v___x_505_;
}
pub unsafe fn l_Lake_InputFileConfig_instConfigFields(
    mut v_name_506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_507_ = l_Lake_InputFileConfig___fields;
    return v___x_507_;
}
pub unsafe fn l_Lake_InputFileConfig_instConfigFields___boxed(
    mut v_name_508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_509_ = l_Lake_InputFileConfig_instConfigFields(v_name_508_);
    crate::leanh::lean_dec(v_name_508_);
    return v_res_509_;
}
pub unsafe fn l_Lake_InputFileConfig_instConfigInfo___lam__0(
    mut v_x1_510_: *mut crate::leanh::LeanObject,
    mut v_x2_511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_512_ = crate::leanh::lean_ctor_get(v_x2_511_, 0);
    crate::leanh::lean_inc(v_name_512_);
    v___x_513_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_name_512_,
        v_x2_511_,
        v_x1_510_,
    );
    return v___x_513_;
}
pub unsafe fn _init_l_Lake_InputFileConfig_instConfigInfo___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_514_ = l_Lake_InputFileConfig___fields;
    v___x_515_ = lean_array_get_size(v___x_514_);
    return v___x_515_;
}
pub unsafe fn _init_l_Lake_InputFileConfig_instConfigInfo___closed__11() -> u8 {
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: u8 = 0;
    v___x_535_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_InputFileConfig_instConfigInfo___closed__0,
    );
    v___x_536_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_537_ = lean_nat_dec_lt(v___x_536_, v___x_535_);
    return v___x_537_;
}
pub unsafe fn _init_l_Lake_InputFileConfig_instConfigInfo___closed__13() -> u8 {
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: u8 = 0;
    v___x_539_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_InputFileConfig_instConfigInfo___closed__0,
    );
    v___x_540_ = lean_nat_dec_le(v___x_539_, v___x_539_);
    return v___x_540_;
}
pub unsafe fn _init_l_Lake_InputFileConfig_instConfigInfo___closed__14() -> usize {
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: usize = 0;
    v___x_541_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_InputFileConfig_instConfigInfo___closed__0,
    );
    v___x_542_ = lean_usize_of_nat(v___x_541_);
    return v___x_542_;
}
pub unsafe fn _init_l_Lake_InputFileConfig_instConfigInfo___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: usize = 0;
    let mut v___x_545_: usize = 0;
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_543_ = crate::leanh::lean_box(1);
    v___x_544_ = crate::leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig_instConfigInfo___closed__14),
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig_instConfigInfo___closed__14_once),
        _init_l_Lake_InputFileConfig_instConfigInfo___closed__14,
    );
    v___x_545_ = 0usize;
    v___x_546_ = l_Lake_InputFileConfig___fields;
    v___f_547_ = l_Lake_InputFileConfig_instConfigInfo___closed__12;
    v___x_548_ = l_Lake_InputFileConfig_instConfigInfo___closed__10;
    v___x_549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_548_,
        v___f_547_,
        v___x_546_,
        v___x_545_,
        v___x_544_,
        v___x_543_,
    );
    return v___x_549_;
}
pub unsafe fn _init_l_Lake_InputFileConfig_instConfigInfo() -> *mut crate::leanh::LeanObject {
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: u8 = 0;
    let mut v___x_557_: u8 = 0;
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_550_ = l_Lake_InputFileConfig___fields;
                v___x_555_ = crate::leanh::lean_box(1);
                v___x_556_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Lake_InputFileConfig_instConfigInfo___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Lake_InputFileConfig_instConfigInfo___closed__11_once
                    ),
                    _init_l_Lake_InputFileConfig_instConfigInfo___closed__11,
                );
                if v___x_556_ == 0 {
                    v___y_552_ = v___x_555_;
                    state = 1;
                    continue;
                } else {
                    v___x_557_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Lake_InputFileConfig_instConfigInfo___closed__13),
                        core::ptr::addr_of_mut!(
                            l_Lake_InputFileConfig_instConfigInfo___closed__13_once
                        ),
                        _init_l_Lake_InputFileConfig_instConfigInfo___closed__13,
                    );
                    if v___x_557_ == 0 {
                        if v___x_556_ == 0 {
                            v___y_552_ = v___x_555_;
                            state = 1;
                            continue;
                        } else {
                            v___x_558_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lake_InputFileConfig_instConfigInfo___closed__15
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lake_InputFileConfig_instConfigInfo___closed__15_once
                                ),
                                _init_l_Lake_InputFileConfig_instConfigInfo___closed__15,
                            );
                            v___y_552_ = v___x_558_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_559_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lake_InputFileConfig_instConfigInfo___closed__15
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lake_InputFileConfig_instConfigInfo___closed__15_once
                            ),
                            _init_l_Lake_InputFileConfig_instConfigInfo___closed__15,
                        );
                        v___y_552_ = v___x_559_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_553_ = crate::leanh::lean_unsigned_to_nat(1);
                crate::leanh::lean_inc(v___y_552_);
                v___x_554_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_554_, 0, v___x_550_);
                crate::leanh::lean_ctor_set(v___x_554_, 1, v___y_552_);
                crate::leanh::lean_ctor_set(v___x_554_, 2, v___x_553_);
                return v___x_554_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputFileConfig_instEmptyCollection(
    mut v_name_560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_561_: u8 = 0;
    let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_561_ = 0;
    v___x_562_ = l_Lean_Name_toString(v_name_560_, v___x_561_);
    v___x_563_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_563_, 0, v___x_562_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_563_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_561_,
    );
    return v___x_563_;
}
pub unsafe fn l_Lake_InputDirConfig_path___proj___lam__0(
    mut v_cfg_564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_path_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_path_565_ = crate::leanh::lean_ctor_get(v_cfg_564_, 0);
    crate::leanh::lean_inc_ref(v_path_565_);
    return v_path_565_;
}
pub unsafe fn l_Lake_InputDirConfig_path___proj___lam__0___boxed(
    mut v_cfg_566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_567_ = l_Lake_InputDirConfig_path___proj___lam__0(v_cfg_566_);
    crate::leanh::lean_dec_ref(v_cfg_566_);
    return v_res_567_;
}
pub unsafe fn l_Lake_InputDirConfig_path___proj___lam__1(
    mut v_val_568_: *mut crate::leanh::LeanObject,
    mut v_cfg_569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_text_570_: u8 = 0;
    let mut v_filter_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_574_: u8 = 0;
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_578_: u8 = 0;
    let mut v_unused_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_text_570_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_569_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_filter_571_ = crate::leanh::lean_ctor_get(v_cfg_569_, 1);
                v_isSharedCheck_578_ = (!crate::leanh::lean_is_exclusive(v_cfg_569_)) as u8;
                if v_isSharedCheck_578_ == 0 {
                    v_unused_579_ = crate::leanh::lean_ctor_get(v_cfg_569_, 0);
                    crate::leanh::lean_dec(v_unused_579_);
                    v___x_573_ = v_cfg_569_;
                    v_isShared_574_ = v_isSharedCheck_578_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_filter_571_);
                    crate::leanh::lean_dec(v_cfg_569_);
                    v___x_573_ = crate::leanh::lean_box(0);
                    v_isShared_574_ = v_isSharedCheck_578_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_574_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_573_, 0, v_val_568_);
                    v___x_576_ = v___x_573_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_577_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_577_, 0, v_val_568_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_577_, 1, v_filter_571_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_577_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_text_570_,
                    );
                    v___x_576_ = v_reuseFailAlloc_577_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_576_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputDirConfig_path___proj___lam__2(
    mut v_f_580_: *mut crate::leanh::LeanObject,
    mut v_cfg_581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_path_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_583_: u8 = 0;
    let mut v_filter_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_587_: u8 = 0;
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_592_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_path_582_ = crate::leanh::lean_ctor_get(v_cfg_581_, 0);
                v_text_583_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_581_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_filter_584_ = crate::leanh::lean_ctor_get(v_cfg_581_, 1);
                v_isSharedCheck_592_ = (!crate::leanh::lean_is_exclusive(v_cfg_581_)) as u8;
                if v_isSharedCheck_592_ == 0 {
                    v___x_586_ = v_cfg_581_;
                    v_isShared_587_ = v_isSharedCheck_592_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_filter_584_);
                    crate::leanh::lean_inc(v_path_582_);
                    crate::leanh::lean_dec(v_cfg_581_);
                    v___x_586_ = crate::leanh::lean_box(0);
                    v_isShared_587_ = v_isSharedCheck_592_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_588_ = crate::leanh::lean_apply_1(v_f_580_, v_path_582_);
                if v_isShared_587_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_586_, 0, v___x_588_);
                    v___x_590_ = v___x_586_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_591_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_591_, 1, v_filter_584_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_591_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_text_583_,
                    );
                    v___x_590_ = v_reuseFailAlloc_591_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_590_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputDirConfig_path___proj___lam__3(
    mut v_name_593_: *mut crate::leanh::LeanObject,
    mut v_x_594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_595_: u8 = 0;
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_595_ = 0;
    v___x_596_ = l_Lean_Name_toString(v_name_593_, v___x_595_);
    return v___x_596_;
}
pub unsafe fn l_Lake_InputDirConfig_path___proj___lam__3___boxed(
    mut v_name_597_: *mut crate::leanh::LeanObject,
    mut v_x_598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_599_ = l_Lake_InputDirConfig_path___proj___lam__3(v_name_597_, v_x_598_);
    crate::leanh::lean_dec_ref(v_x_598_);
    return v_res_599_;
}
pub unsafe fn l_Lake_InputDirConfig_path___proj(
    mut v_name_603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_604_ = l_Lake_InputDirConfig_path___proj___closed__0;
    v___f_605_ = l_Lake_InputDirConfig_path___proj___closed__1;
    v___f_606_ = l_Lake_InputDirConfig_path___proj___closed__2;
    v___f_607_ = crate::leanh::lean_alloc_closure(
        l_Lake_InputDirConfig_path___proj___lam__3___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_607_, 0, v_name_603_);
    v___x_608_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_608_, 0, v___f_604_);
    crate::leanh::lean_ctor_set(v___x_608_, 1, v___f_605_);
    crate::leanh::lean_ctor_set(v___x_608_, 2, v___f_606_);
    crate::leanh::lean_ctor_set(v___x_608_, 3, v___f_607_);
    return v___x_608_;
}
pub unsafe fn l_Lake_InputDirConfig_path_instConfigField(
    mut v_name_609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_610_ = l_Lake_InputDirConfig_path___proj(v_name_609_);
    return v___x_610_;
}
pub unsafe fn l_Lake_InputDirConfig_text___proj___lam__0(
    mut v_cfg_611_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_text_612_: u8 = 0;
    v_text_612_ = crate::leanh::lean_ctor_get_uint8(
        v_cfg_611_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    return v_text_612_;
}
pub unsafe fn l_Lake_InputDirConfig_text___proj___lam__0___boxed(
    mut v_cfg_613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_614_: u8 = 0;
    let mut v_r_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_614_ = l_Lake_InputDirConfig_text___proj___lam__0(v_cfg_613_);
    crate::leanh::lean_dec_ref(v_cfg_613_);
    v_r_615_ = crate::leanh::lean_box((v_res_614_) as usize);
    return v_r_615_;
}
pub unsafe fn l_Lake_InputDirConfig_text___proj___lam__1(
    mut v_val_616_: u8,
    mut v_cfg_617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_path_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_filter_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_622_: u8 = 0;
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_626_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_path_618_ = crate::leanh::lean_ctor_get(v_cfg_617_, 0);
                v_filter_619_ = crate::leanh::lean_ctor_get(v_cfg_617_, 1);
                v_isSharedCheck_626_ = (!crate::leanh::lean_is_exclusive(v_cfg_617_)) as u8;
                if v_isSharedCheck_626_ == 0 {
                    v___x_621_ = v_cfg_617_;
                    v_isShared_622_ = v_isSharedCheck_626_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_filter_619_);
                    crate::leanh::lean_inc(v_path_618_);
                    crate::leanh::lean_dec(v_cfg_617_);
                    v___x_621_ = crate::leanh::lean_box(0);
                    v_isShared_622_ = v_isSharedCheck_626_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_622_ == 0 {
                    v___x_624_ = v___x_621_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_625_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_625_, 0, v_path_618_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_625_, 1, v_filter_619_);
                    v___x_624_ = v_reuseFailAlloc_625_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_624_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_val_616_,
                );
                return v___x_624_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputDirConfig_text___proj___lam__1___boxed(
    mut v_val_627_: *mut crate::leanh::LeanObject,
    mut v_cfg_628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_44__boxed_629_: u8 = 0;
    let mut v_res_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_44__boxed_629_ = (crate::leanh::lean_unbox(v_val_627_) as u8);
    v_res_630_ = l_Lake_InputDirConfig_text___proj___lam__1(v_val_44__boxed_629_, v_cfg_628_);
    return v_res_630_;
}
pub unsafe fn l_Lake_InputDirConfig_text___proj___lam__2(
    mut v_f_631_: *mut crate::leanh::LeanObject,
    mut v_cfg_632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_path_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_634_: u8 = 0;
    let mut v_filter_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_638_: u8 = 0;
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: u8 = 0;
    let mut v_reuseFailAlloc_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_645_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_path_633_ = crate::leanh::lean_ctor_get(v_cfg_632_, 0);
                v_text_634_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_632_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_filter_635_ = crate::leanh::lean_ctor_get(v_cfg_632_, 1);
                v_isSharedCheck_645_ = (!crate::leanh::lean_is_exclusive(v_cfg_632_)) as u8;
                if v_isSharedCheck_645_ == 0 {
                    v___x_637_ = v_cfg_632_;
                    v_isShared_638_ = v_isSharedCheck_645_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_filter_635_);
                    crate::leanh::lean_inc(v_path_633_);
                    crate::leanh::lean_dec(v_cfg_632_);
                    v___x_637_ = crate::leanh::lean_box(0);
                    v_isShared_638_ = v_isSharedCheck_645_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_639_ = crate::leanh::lean_box((v_text_634_) as usize);
                v___x_640_ = crate::leanh::lean_apply_1(v_f_631_, v___x_639_);
                if v_isShared_638_ == 0 {
                    v___x_642_ = v___x_637_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_644_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_644_, 0, v_path_633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_644_, 1, v_filter_635_);
                    v___x_642_ = v_reuseFailAlloc_644_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_643_ = (crate::leanh::lean_unbox(v___x_640_) as u8);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_642_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_643_,
                );
                return v___x_642_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputDirConfig_text___proj___lam__3(
    mut v_x_646_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_647_: u8 = 0;
    v___x_647_ = 0;
    return v___x_647_;
}
pub unsafe fn l_Lake_InputDirConfig_text___proj___lam__3___boxed(
    mut v_x_648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_649_: u8 = 0;
    let mut v_r_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_649_ = l_Lake_InputDirConfig_text___proj___lam__3(v_x_648_);
    crate::leanh::lean_dec_ref(v_x_648_);
    v_r_650_ = crate::leanh::lean_box((v_res_649_) as usize);
    return v_r_650_;
}
pub unsafe fn l_Lake_InputDirConfig_text___proj(
    mut v_name_660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_661_ = l_Lake_InputDirConfig_text___proj___closed__4;
    return v___x_661_;
}
pub unsafe fn l_Lake_InputDirConfig_text___proj___boxed(
    mut v_name_662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_663_ = l_Lake_InputDirConfig_text___proj(v_name_662_);
    crate::leanh::lean_dec(v_name_662_);
    return v_res_663_;
}
pub unsafe fn l_Lake_InputDirConfig_text_instConfigField(
    mut v_name_664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_665_ = l_Lake_InputDirConfig_text___proj(v_name_664_);
    return v___x_665_;
}
pub unsafe fn l_Lake_InputDirConfig_text_instConfigField___boxed(
    mut v_name_666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_667_ = l_Lake_InputDirConfig_text_instConfigField(v_name_666_);
    crate::leanh::lean_dec(v_name_666_);
    return v_res_667_;
}
pub unsafe fn l_Lake_InputDirConfig_filter___proj___lam__0(
    mut v_cfg_668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_filter_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_filter_669_ = crate::leanh::lean_ctor_get(v_cfg_668_, 1);
    crate::leanh::lean_inc_ref(v_filter_669_);
    return v_filter_669_;
}
pub unsafe fn l_Lake_InputDirConfig_filter___proj___lam__0___boxed(
    mut v_cfg_670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_671_ = l_Lake_InputDirConfig_filter___proj___lam__0(v_cfg_670_);
    crate::leanh::lean_dec_ref(v_cfg_670_);
    return v_res_671_;
}
pub unsafe fn l_Lake_InputDirConfig_filter___proj___lam__1(
    mut v_val_672_: *mut crate::leanh::LeanObject,
    mut v_cfg_673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_path_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_675_: u8 = 0;
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_678_: u8 = 0;
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_682_: u8 = 0;
    let mut v_unused_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_path_674_ = crate::leanh::lean_ctor_get(v_cfg_673_, 0);
                v_text_675_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_673_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_682_ = (!crate::leanh::lean_is_exclusive(v_cfg_673_)) as u8;
                if v_isSharedCheck_682_ == 0 {
                    v_unused_683_ = crate::leanh::lean_ctor_get(v_cfg_673_, 1);
                    crate::leanh::lean_dec(v_unused_683_);
                    v___x_677_ = v_cfg_673_;
                    v_isShared_678_ = v_isSharedCheck_682_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_path_674_);
                    crate::leanh::lean_dec(v_cfg_673_);
                    v___x_677_ = crate::leanh::lean_box(0);
                    v_isShared_678_ = v_isSharedCheck_682_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_678_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_677_, 1, v_val_672_);
                    v___x_680_ = v___x_677_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_681_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_681_, 0, v_path_674_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_681_, 1, v_val_672_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_681_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_text_675_,
                    );
                    v___x_680_ = v_reuseFailAlloc_681_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_680_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputDirConfig_filter___proj___lam__2(
    mut v_f_684_: *mut crate::leanh::LeanObject,
    mut v_cfg_685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_path_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_687_: u8 = 0;
    let mut v_filter_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_691_: u8 = 0;
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_696_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_path_686_ = crate::leanh::lean_ctor_get(v_cfg_685_, 0);
                v_text_687_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_685_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_filter_688_ = crate::leanh::lean_ctor_get(v_cfg_685_, 1);
                v_isSharedCheck_696_ = (!crate::leanh::lean_is_exclusive(v_cfg_685_)) as u8;
                if v_isSharedCheck_696_ == 0 {
                    v___x_690_ = v_cfg_685_;
                    v_isShared_691_ = v_isSharedCheck_696_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_filter_688_);
                    crate::leanh::lean_inc(v_path_686_);
                    crate::leanh::lean_dec(v_cfg_685_);
                    v___x_690_ = crate::leanh::lean_box(0);
                    v_isShared_691_ = v_isSharedCheck_696_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_692_ = crate::leanh::lean_apply_1(v_f_684_, v_filter_688_);
                if v_isShared_691_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_690_, 1, v___x_692_);
                    v___x_694_ = v___x_690_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_695_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_695_, 0, v_path_686_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_695_, 1, v___x_692_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_695_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_text_687_,
                    );
                    v___x_694_ = v_reuseFailAlloc_695_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_694_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lake_InputDirConfig_filter___proj___lam__3___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_697_ = l_Lake_Pattern_star(crate::leanh::lean_box(0), crate::leanh::lean_box(0));
    return v___x_697_;
}
pub unsafe fn l_Lake_InputDirConfig_filter___proj___lam__3(
    mut v_x_698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_699_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_filter___proj___lam__3___closed__0),
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_filter___proj___lam__3___closed__0_once),
        _init_l_Lake_InputDirConfig_filter___proj___lam__3___closed__0,
    );
    return v___x_699_;
}
pub unsafe fn l_Lake_InputDirConfig_filter___proj___lam__3___boxed(
    mut v_x_700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_701_ = l_Lake_InputDirConfig_filter___proj___lam__3(v_x_700_);
    crate::leanh::lean_dec_ref(v_x_700_);
    return v_res_701_;
}
pub unsafe fn l_Lake_InputDirConfig_filter___proj(
    mut v_name_711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_712_ = l_Lake_InputDirConfig_filter___proj___closed__4;
    return v___x_712_;
}
pub unsafe fn l_Lake_InputDirConfig_filter___proj___boxed(
    mut v_name_713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_714_ = l_Lake_InputDirConfig_filter___proj(v_name_713_);
    crate::leanh::lean_dec(v_name_713_);
    return v_res_714_;
}
pub unsafe fn l_Lake_InputDirConfig_filter_instConfigField(
    mut v_name_715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_716_ = l_Lake_InputDirConfig_filter___proj(v_name_715_);
    return v___x_716_;
}
pub unsafe fn l_Lake_InputDirConfig_filter_instConfigField___boxed(
    mut v_name_717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_718_ = l_Lake_InputDirConfig_filter_instConfigField(v_name_717_);
    crate::leanh::lean_dec(v_name_717_);
    return v_res_718_;
}
pub unsafe fn _init_l_Lake_InputDirConfig___fields___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_726_ = l_Lake_InputDirConfig___fields___closed__2;
    v___x_727_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig___fields___closed__8),
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig___fields___closed__8_once),
        _init_l_Lake_InputFileConfig___fields___closed__8,
    );
    v___x_728_ = lean_array_push(v___x_727_, v___x_726_);
    return v___x_728_;
}
pub unsafe fn _init_l_Lake_InputDirConfig___fields() -> *mut crate::leanh::LeanObject {
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_729_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig___fields___closed__3),
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig___fields___closed__3_once),
        _init_l_Lake_InputDirConfig___fields___closed__3,
    );
    return v___x_729_;
}
pub unsafe fn l_Lake_InputDirConfig_instConfigFields(
    mut v_name_730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_731_ = l_Lake_InputDirConfig___fields;
    return v___x_731_;
}
pub unsafe fn l_Lake_InputDirConfig_instConfigFields___boxed(
    mut v_name_732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_733_ = l_Lake_InputDirConfig_instConfigFields(v_name_732_);
    crate::leanh::lean_dec(v_name_732_);
    return v_res_733_;
}
pub unsafe fn _init_l_Lake_InputDirConfig_instConfigInfo___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_734_ = l_Lake_InputDirConfig___fields;
    v___x_735_ = lean_array_get_size(v___x_734_);
    return v___x_735_;
}
pub unsafe fn _init_l_Lake_InputDirConfig_instConfigInfo___closed__1() -> u8 {
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: u8 = 0;
    v___x_736_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_InputDirConfig_instConfigInfo___closed__0,
    );
    v___x_737_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_738_ = lean_nat_dec_lt(v___x_737_, v___x_736_);
    return v___x_738_;
}
pub unsafe fn _init_l_Lake_InputDirConfig_instConfigInfo___closed__2() -> u8 {
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: u8 = 0;
    v___x_739_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_InputDirConfig_instConfigInfo___closed__0,
    );
    v___x_740_ = lean_nat_dec_le(v___x_739_, v___x_739_);
    return v___x_740_;
}
pub unsafe fn _init_l_Lake_InputDirConfig_instConfigInfo___closed__3() -> usize {
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: usize = 0;
    v___x_741_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_InputDirConfig_instConfigInfo___closed__0,
    );
    v___x_742_ = lean_usize_of_nat(v___x_741_);
    return v___x_742_;
}
pub unsafe fn _init_l_Lake_InputDirConfig_instConfigInfo___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: usize = 0;
    let mut v___x_745_: usize = 0;
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_743_ = crate::leanh::lean_box(1);
    v___x_744_ = crate::leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_instConfigInfo___closed__3),
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_instConfigInfo___closed__3_once),
        _init_l_Lake_InputDirConfig_instConfigInfo___closed__3,
    );
    v___x_745_ = 0usize;
    v___x_746_ = l_Lake_InputDirConfig___fields;
    v___f_747_ = l_Lake_InputFileConfig_instConfigInfo___closed__12;
    v___x_748_ = l_Lake_InputFileConfig_instConfigInfo___closed__10;
    v___x_749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_748_,
        v___f_747_,
        v___x_746_,
        v___x_745_,
        v___x_744_,
        v___x_743_,
    );
    return v___x_749_;
}
pub unsafe fn _init_l_Lake_InputDirConfig_instConfigInfo() -> *mut crate::leanh::LeanObject {
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: u8 = 0;
    let mut v___x_757_: u8 = 0;
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_750_ = l_Lake_InputDirConfig___fields;
                v___x_755_ = crate::leanh::lean_box(1);
                v___x_756_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Lake_InputDirConfig_instConfigInfo___closed__1),
                    core::ptr::addr_of_mut!(l_Lake_InputDirConfig_instConfigInfo___closed__1_once),
                    _init_l_Lake_InputDirConfig_instConfigInfo___closed__1,
                );
                if v___x_756_ == 0 {
                    v___y_752_ = v___x_755_;
                    state = 1;
                    continue;
                } else {
                    v___x_757_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_instConfigInfo___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Lake_InputDirConfig_instConfigInfo___closed__2_once
                        ),
                        _init_l_Lake_InputDirConfig_instConfigInfo___closed__2,
                    );
                    if v___x_757_ == 0 {
                        if v___x_756_ == 0 {
                            v___y_752_ = v___x_755_;
                            state = 1;
                            continue;
                        } else {
                            v___x_758_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lake_InputDirConfig_instConfigInfo___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lake_InputDirConfig_instConfigInfo___closed__4_once
                                ),
                                _init_l_Lake_InputDirConfig_instConfigInfo___closed__4,
                            );
                            v___y_752_ = v___x_758_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_759_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lake_InputDirConfig_instConfigInfo___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lake_InputDirConfig_instConfigInfo___closed__4_once
                            ),
                            _init_l_Lake_InputDirConfig_instConfigInfo___closed__4,
                        );
                        v___y_752_ = v___x_759_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_753_ = crate::leanh::lean_unsigned_to_nat(1);
                crate::leanh::lean_inc(v___y_752_);
                v___x_754_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_754_, 0, v___x_750_);
                crate::leanh::lean_ctor_set(v___x_754_, 1, v___y_752_);
                crate::leanh::lean_ctor_set(v___x_754_, 2, v___x_753_);
                return v___x_754_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputDirConfig_instEmptyCollection(
    mut v_name_760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_761_: u8 = 0;
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_761_ = 0;
    v___x_762_ = l_Lean_Name_toString(v_name_760_, v___x_761_);
    v___x_763_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_filter___proj___lam__3___closed__0),
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_filter___proj___lam__3___closed__0_once),
        _init_l_Lake_InputDirConfig_filter___proj___lam__3___closed__0,
    );
    v___x_764_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_764_, 0, v___x_762_);
    crate::leanh::lean_ctor_set(v___x_764_, 1, v___x_763_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_764_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v___x_761_,
    );
    return v___x_764_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_InputFileConfig(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Pattern(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_MetaClasses(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lake_InputFileConfig___fields = _init_l_Lake_InputFileConfig___fields();
    crate::leanh::lean_mark_persistent(l_Lake_InputFileConfig___fields);
    l_Lake_InputFileConfig_instConfigInfo = _init_l_Lake_InputFileConfig_instConfigInfo();
    crate::leanh::lean_mark_persistent(l_Lake_InputFileConfig_instConfigInfo);
    l_Lake_InputDirConfig___fields = _init_l_Lake_InputDirConfig___fields();
    crate::leanh::lean_mark_persistent(l_Lake_InputDirConfig___fields);
    l_Lake_InputDirConfig_instConfigInfo = _init_l_Lake_InputDirConfig_instConfigInfo();
    crate::leanh::lean_mark_persistent(l_Lake_InputDirConfig_instConfigInfo);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_InputFileConfig(
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
pub unsafe fn initialize_Lake_Config_InputFileConfig(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Pattern(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_MetaClasses(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Name(builtin);
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
    res = runtime_initialize_Lake_Config_InputFileConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_InputFileConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Config_InputFileConfig(builtin);
}
