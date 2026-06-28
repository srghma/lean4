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
    initialize_Lake_Config_Meta, meta_initialize_Lake_Config_Meta,
    runtime_initialize_Lake_Config_Meta,
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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_uint8_once, lean_unbox,
    lean_unsigned_to_nat, lean_usize_once,
};
pub static l_Lake_InputFileConfig_path___proj___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_InputFileConfig_path___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputFileConfig_path___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_path___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_InputFileConfig_path___proj___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_InputFileConfig_path___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputFileConfig_path___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_path___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_InputFileConfig_path___proj___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_InputFileConfig_path___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputFileConfig_path___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_path___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_InputFileConfig_text___proj___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_InputFileConfig_text___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputFileConfig_text___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_text___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_InputFileConfig_text___proj___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_InputFileConfig_text___proj___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputFileConfig_text___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_text___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_InputFileConfig_text___proj___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_InputFileConfig_text___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputFileConfig_text___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_text___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_InputFileConfig_text___proj___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_InputFileConfig_text___proj___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputFileConfig_text___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_text___proj___closed__3_value) as *mut LeanObject;
pub static l_Lake_InputFileConfig_text___proj___closed__4_value: LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Lake_InputFileConfig_text___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_InputFileConfig_text___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_InputFileConfig_text___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_InputFileConfig_text___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_InputFileConfig_text___proj___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_text___proj___closed__4_value) as *mut LeanObject;
pub static l_Lake_InputFileConfig___fields___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lake_InputFileConfig___fields___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__0_value) as *mut LeanObject;
pub static l_Lake_InputFileConfig___fields___closed__1_value: LeanStringObject<5> =
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
        m_data: [112, 97, 116, 104, 0],
    };
static mut l_Lake_InputFileConfig___fields___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__1_value) as *mut LeanObject;
pub static l_Lake_InputFileConfig___fields___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__1_value) as *mut LeanObject,
        1599759234323164429 as *mut LeanObject,
    ],
};
static mut l_Lake_InputFileConfig___fields___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__2_value) as *mut LeanObject;
pub static l_Lake_InputFileConfig___fields___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__2_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_InputFileConfig___fields___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__3_value) as *mut LeanObject;
static mut l_Lake_InputFileConfig___fields___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_InputFileConfig___fields___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_InputFileConfig___fields___closed__5_value: LeanStringObject<5> =
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
        m_data: [116, 101, 120, 116, 0],
    };
static mut l_Lake_InputFileConfig___fields___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__5_value) as *mut LeanObject;
pub static l_Lake_InputFileConfig___fields___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__5_value) as *mut LeanObject,
        11956103831239991322 as *mut LeanObject,
    ],
};
static mut l_Lake_InputFileConfig___fields___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__6_value) as *mut LeanObject;
pub static l_Lake_InputFileConfig___fields___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__6_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_InputFileConfig___fields___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig___fields___closed__7_value) as *mut LeanObject;
static mut l_Lake_InputFileConfig___fields___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_InputFileConfig___fields___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_InputFileConfig___fields: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_InputFileConfig_instConfigInfo___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_InputFileConfig_instConfigInfo___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_InputFileConfig_instConfigInfo___closed__1_value: LeanClosureObject<0> =
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
static mut l_Lake_InputFileConfig_instConfigInfo___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__1_value) as *mut LeanObject;
pub static l_Lake_InputFileConfig_instConfigInfo___closed__2_value: LeanClosureObject<0> =
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
static mut l_Lake_InputFileConfig_instConfigInfo___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__2_value) as *mut LeanObject;
pub static l_Lake_InputFileConfig_instConfigInfo___closed__3_value: LeanClosureObject<0> =
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
static mut l_Lake_InputFileConfig_instConfigInfo___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__3_value) as *mut LeanObject;
pub static l_Lake_InputFileConfig_instConfigInfo___closed__4_value: LeanClosureObject<0> =
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
static mut l_Lake_InputFileConfig_instConfigInfo___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__4_value) as *mut LeanObject;
pub static l_Lake_InputFileConfig_instConfigInfo___closed__5_value: LeanClosureObject<0> =
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
static mut l_Lake_InputFileConfig_instConfigInfo___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__5_value) as *mut LeanObject;
pub static l_Lake_InputFileConfig_instConfigInfo___closed__6_value: LeanClosureObject<0> =
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
static mut l_Lake_InputFileConfig_instConfigInfo___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__6_value) as *mut LeanObject;
pub static l_Lake_InputFileConfig_instConfigInfo___closed__7_value: LeanClosureObject<0> =
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
static mut l_Lake_InputFileConfig_instConfigInfo___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__7_value) as *mut LeanObject;
pub static l_Lake_InputFileConfig_instConfigInfo___closed__8_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_InputFileConfig_instConfigInfo___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__8_value) as *mut LeanObject;
pub static l_Lake_InputFileConfig_instConfigInfo___closed__9_value: LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_InputFileConfig_instConfigInfo___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__9_value) as *mut LeanObject;
pub static l_Lake_InputFileConfig_instConfigInfo___closed__10_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_InputFileConfig_instConfigInfo___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__10_value)
        as *mut LeanObject;
static mut l_Lake_InputFileConfig_instConfigInfo___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_InputFileConfig_instConfigInfo___closed__11: u8 = 0;
pub static l_Lake_InputFileConfig_instConfigInfo___closed__12_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_InputFileConfig_instConfigInfo___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputFileConfig_instConfigInfo___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputFileConfig_instConfigInfo___closed__12_value)
        as *mut LeanObject;
static mut l_Lake_InputFileConfig_instConfigInfo___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_InputFileConfig_instConfigInfo___closed__13: u8 = 0;
static mut l_Lake_InputFileConfig_instConfigInfo___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_InputFileConfig_instConfigInfo___closed__14: usize = 0;
static mut l_Lake_InputFileConfig_instConfigInfo___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_InputFileConfig_instConfigInfo___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_InputFileConfig_instConfigInfo: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_InputDirConfig_path___proj___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_InputDirConfig_path___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputDirConfig_path___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_path___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_InputDirConfig_path___proj___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_InputDirConfig_path___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputDirConfig_path___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_path___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_InputDirConfig_path___proj___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_InputDirConfig_path___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputDirConfig_path___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_path___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_InputDirConfig_text___proj___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_InputDirConfig_text___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputDirConfig_text___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_text___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_InputDirConfig_text___proj___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_InputDirConfig_text___proj___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputDirConfig_text___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_text___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_InputDirConfig_text___proj___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_InputDirConfig_text___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputDirConfig_text___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_text___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_InputDirConfig_text___proj___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_InputDirConfig_text___proj___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputDirConfig_text___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_text___proj___closed__3_value) as *mut LeanObject;
pub static l_Lake_InputDirConfig_text___proj___closed__4_value: LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Lake_InputDirConfig_text___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_InputDirConfig_text___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_InputDirConfig_text___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_InputDirConfig_text___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_InputDirConfig_text___proj___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_text___proj___closed__4_value) as *mut LeanObject;
static mut l_Lake_InputDirConfig_filter___proj___lam__3___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_InputDirConfig_filter___proj___lam__3___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_InputDirConfig_filter___proj___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_InputDirConfig_filter___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputDirConfig_filter___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_filter___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_InputDirConfig_filter___proj___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_InputDirConfig_filter___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputDirConfig_filter___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_filter___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_InputDirConfig_filter___proj___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_InputDirConfig_filter___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputDirConfig_filter___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_filter___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_InputDirConfig_filter___proj___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_InputDirConfig_filter___proj___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_InputDirConfig_filter___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_filter___proj___closed__3_value) as *mut LeanObject;
pub static l_Lake_InputDirConfig_filter___proj___closed__4_value: LeanCtorObject<4> =
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
            core::ptr::addr_of!(l_Lake_InputDirConfig_filter___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_InputDirConfig_filter___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_InputDirConfig_filter___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_InputDirConfig_filter___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_InputDirConfig_filter___proj___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig_filter___proj___closed__4_value) as *mut LeanObject;
pub static l_Lake_InputDirConfig___fields___closed__0_value: LeanStringObject<7> =
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
        m_data: [102, 105, 108, 116, 101, 114, 0],
    };
static mut l_Lake_InputDirConfig___fields___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig___fields___closed__0_value) as *mut LeanObject;
pub static l_Lake_InputDirConfig___fields___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_InputDirConfig___fields___closed__0_value) as *mut LeanObject,
        11672201034198194596 as *mut LeanObject,
    ],
};
static mut l_Lake_InputDirConfig___fields___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig___fields___closed__1_value) as *mut LeanObject;
pub static l_Lake_InputDirConfig___fields___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_InputDirConfig___fields___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_InputDirConfig___fields___closed__1_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_InputDirConfig___fields___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_InputDirConfig___fields___closed__2_value) as *mut LeanObject;
static mut l_Lake_InputDirConfig___fields___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_InputDirConfig___fields___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_InputDirConfig___fields: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_InputDirConfig_instConfigInfo___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_InputDirConfig_instConfigInfo___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_InputDirConfig_instConfigInfo___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_InputDirConfig_instConfigInfo___closed__1: u8 = 0;
static mut l_Lake_InputDirConfig_instConfigInfo___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_InputDirConfig_instConfigInfo___closed__2: u8 = 0;
static mut l_Lake_InputDirConfig_instConfigInfo___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_InputDirConfig_instConfigInfo___closed__3: usize = 0;
static mut l_Lake_InputDirConfig_instConfigInfo___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_InputDirConfig_instConfigInfo___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_InputDirConfig_instConfigInfo: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lake_InputFileConfig_path___proj___lam__0(
    mut v_cfg_383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_path_384_: *mut LeanObject = core::ptr::null_mut();
    v_path_384_ = lean_ctor_get(v_cfg_383_, 0);
    lean_inc_ref(v_path_384_);
    return v_path_384_;
}
pub unsafe fn l_Lake_InputFileConfig_path___proj___lam__0___boxed(
    mut v_cfg_385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_386_: *mut LeanObject = core::ptr::null_mut();
    v_res_386_ = l_Lake_InputFileConfig_path___proj___lam__0(v_cfg_385_);
    lean_dec_ref(v_cfg_385_);
    return v_res_386_;
}
pub unsafe fn l_Lake_InputFileConfig_path___proj___lam__1(
    mut v_val_387_: *mut LeanObject,
    mut v_cfg_388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_text_389_: u8 = 0;
    let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_392_: u8 = 0;
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_396_: u8 = 0;
    let mut v_unused_397_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_text_389_ = lean_ctor_get_uint8(
                    v_cfg_388_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_396_ = (!lean_is_exclusive(v_cfg_388_)) as u8;
                if v_isSharedCheck_396_ == 0 {
                    v_unused_397_ = lean_ctor_get(v_cfg_388_, 0);
                    lean_dec(v_unused_397_);
                    v___x_391_ = v_cfg_388_;
                    v_isShared_392_ = v_isSharedCheck_396_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_cfg_388_);
                    v___x_391_ = lean_box(0);
                    v_isShared_392_ = v_isSharedCheck_396_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_392_ == 0 {
                    lean_ctor_set(v___x_391_, 0, v_val_387_);
                    v___x_394_ = v___x_391_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_395_, 0, v_val_387_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_395_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_f_398_: *mut LeanObject,
    mut v_cfg_399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_path_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_401_: u8 = 0;
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_404_: u8 = 0;
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_409_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_path_400_ = lean_ctor_get(v_cfg_399_, 0);
                v_text_401_ = lean_ctor_get_uint8(
                    v_cfg_399_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_409_ = (!lean_is_exclusive(v_cfg_399_)) as u8;
                if v_isSharedCheck_409_ == 0 {
                    v___x_403_ = v_cfg_399_;
                    v_isShared_404_ = v_isSharedCheck_409_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_path_400_);
                    lean_dec(v_cfg_399_);
                    v___x_403_ = lean_box(0);
                    v_isShared_404_ = v_isSharedCheck_409_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_405_ = lean_apply_1(v_f_398_, v_path_400_);
                if v_isShared_404_ == 0 {
                    lean_ctor_set(v___x_403_, 0, v___x_405_);
                    v___x_407_ = v___x_403_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_408_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_name_410_: *mut LeanObject,
    mut v_x_411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_412_: u8 = 0;
    let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
    v___x_412_ = 0;
    v___x_413_ = l_Lean_Name_toString(v_name_410_, v___x_412_);
    return v___x_413_;
}
pub unsafe fn l_Lake_InputFileConfig_path___proj___lam__3___boxed(
    mut v_name_414_: *mut LeanObject,
    mut v_x_415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_416_: *mut LeanObject = core::ptr::null_mut();
    v_res_416_ = l_Lake_InputFileConfig_path___proj___lam__3(v_name_414_, v_x_415_);
    lean_dec_ref(v_x_415_);
    return v_res_416_;
}
pub unsafe fn l_Lake_InputFileConfig_path___proj(
    mut v_name_420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
    v___f_421_ = l_Lake_InputFileConfig_path___proj___closed__0;
    v___f_422_ = l_Lake_InputFileConfig_path___proj___closed__1;
    v___f_423_ = l_Lake_InputFileConfig_path___proj___closed__2;
    v___f_424_ = lean_alloc_closure(
        l_Lake_InputFileConfig_path___proj___lam__3___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_424_, 0, v_name_420_);
    v___x_425_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_425_, 0, v___f_421_);
    lean_ctor_set(v___x_425_, 1, v___f_422_);
    lean_ctor_set(v___x_425_, 2, v___f_423_);
    lean_ctor_set(v___x_425_, 3, v___f_424_);
    return v___x_425_;
}
pub unsafe fn l_Lake_InputFileConfig_path_instConfigField(
    mut v_name_426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_427_: *mut LeanObject = core::ptr::null_mut();
    v___x_427_ = l_Lake_InputFileConfig_path___proj(v_name_426_);
    return v___x_427_;
}
pub unsafe fn l_Lake_InputFileConfig_text___proj___lam__0(mut v_cfg_428_: *mut LeanObject) -> u8 {
    let mut v_text_429_: u8 = 0;
    v_text_429_ = lean_ctor_get_uint8(
        v_cfg_428_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    return v_text_429_;
}
pub unsafe fn l_Lake_InputFileConfig_text___proj___lam__0___boxed(
    mut v_cfg_430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_431_: u8 = 0;
    let mut v_r_432_: *mut LeanObject = core::ptr::null_mut();
    v_res_431_ = l_Lake_InputFileConfig_text___proj___lam__0(v_cfg_430_);
    lean_dec_ref(v_cfg_430_);
    v_r_432_ = lean_box((v_res_431_) as usize);
    return v_r_432_;
}
pub unsafe fn l_Lake_InputFileConfig_text___proj___lam__1(
    mut v_val_433_: u8,
    mut v_cfg_434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_path_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_438_: u8 = 0;
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_442_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_path_435_ = lean_ctor_get(v_cfg_434_, 0);
                v_isSharedCheck_442_ = (!lean_is_exclusive(v_cfg_434_)) as u8;
                if v_isSharedCheck_442_ == 0 {
                    v___x_437_ = v_cfg_434_;
                    v_isShared_438_ = v_isSharedCheck_442_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_path_435_);
                    lean_dec(v_cfg_434_);
                    v___x_437_ = lean_box(0);
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
                    v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_441_, 0, v_path_435_);
                    v___x_440_ = v_reuseFailAlloc_441_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_440_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_val_433_,
                );
                return v___x_440_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputFileConfig_text___proj___lam__1___boxed(
    mut v_val_443_: *mut LeanObject,
    mut v_cfg_444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_41__boxed_445_: u8 = 0;
    let mut v_res_446_: *mut LeanObject = core::ptr::null_mut();
    v_val_41__boxed_445_ = (lean_unbox(v_val_443_) as u8);
    v_res_446_ = l_Lake_InputFileConfig_text___proj___lam__1(v_val_41__boxed_445_, v_cfg_444_);
    return v_res_446_;
}
pub unsafe fn l_Lake_InputFileConfig_text___proj___lam__2(
    mut v_f_447_: *mut LeanObject,
    mut v_cfg_448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_path_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_450_: u8 = 0;
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_453_: u8 = 0;
    let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_458_: u8 = 0;
    let mut v_reuseFailAlloc_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_460_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_path_449_ = lean_ctor_get(v_cfg_448_, 0);
                v_text_450_ = lean_ctor_get_uint8(
                    v_cfg_448_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_460_ = (!lean_is_exclusive(v_cfg_448_)) as u8;
                if v_isSharedCheck_460_ == 0 {
                    v___x_452_ = v_cfg_448_;
                    v_isShared_453_ = v_isSharedCheck_460_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_path_449_);
                    lean_dec(v_cfg_448_);
                    v___x_452_ = lean_box(0);
                    v_isShared_453_ = v_isSharedCheck_460_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_454_ = lean_box((v_text_450_) as usize);
                v___x_455_ = lean_apply_1(v_f_447_, v___x_454_);
                if v_isShared_453_ == 0 {
                    v___x_457_ = v___x_452_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_459_, 0, v_path_449_);
                    v___x_457_ = v_reuseFailAlloc_459_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_458_ = (lean_unbox(v___x_455_) as u8);
                lean_ctor_set_uint8(
                    v___x_457_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_458_,
                );
                return v___x_457_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputFileConfig_text___proj___lam__3(mut v_x_461_: *mut LeanObject) -> u8 {
    let mut v___x_462_: u8 = 0;
    v___x_462_ = 0;
    return v___x_462_;
}
pub unsafe fn l_Lake_InputFileConfig_text___proj___lam__3___boxed(
    mut v_x_463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_464_: u8 = 0;
    let mut v_r_465_: *mut LeanObject = core::ptr::null_mut();
    v_res_464_ = l_Lake_InputFileConfig_text___proj___lam__3(v_x_463_);
    lean_dec_ref(v_x_463_);
    v_r_465_ = lean_box((v_res_464_) as usize);
    return v_r_465_;
}
pub unsafe fn l_Lake_InputFileConfig_text___proj(
    mut v_name_475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    v___x_476_ = l_Lake_InputFileConfig_text___proj___closed__4;
    return v___x_476_;
}
pub unsafe fn l_Lake_InputFileConfig_text___proj___boxed(
    mut v_name_477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_478_: *mut LeanObject = core::ptr::null_mut();
    v_res_478_ = l_Lake_InputFileConfig_text___proj(v_name_477_);
    lean_dec(v_name_477_);
    return v_res_478_;
}
pub unsafe fn l_Lake_InputFileConfig_text_instConfigField(
    mut v_name_479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    v___x_480_ = l_Lake_InputFileConfig_text___proj(v_name_479_);
    return v___x_480_;
}
pub unsafe fn l_Lake_InputFileConfig_text_instConfigField___boxed(
    mut v_name_481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_482_: *mut LeanObject = core::ptr::null_mut();
    v_res_482_ = l_Lake_InputFileConfig_text_instConfigField(v_name_481_);
    lean_dec(v_name_481_);
    return v_res_482_;
}
pub unsafe fn _init_l_Lake_InputFileConfig___fields___closed__4() -> *mut LeanObject {
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    v___x_492_ = l_Lake_InputFileConfig___fields___closed__3;
    v___x_493_ = l_Lake_InputFileConfig___fields___closed__0;
    v___x_494_ = lean_array_push(v___x_493_, v___x_492_);
    return v___x_494_;
}
pub unsafe fn _init_l_Lake_InputFileConfig___fields___closed__8() -> *mut LeanObject {
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    v___x_502_ = l_Lake_InputFileConfig___fields___closed__7;
    v___x_503_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig___fields___closed__4),
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig___fields___closed__4_once),
        _init_l_Lake_InputFileConfig___fields___closed__4,
    );
    v___x_504_ = lean_array_push(v___x_503_, v___x_502_);
    return v___x_504_;
}
pub unsafe fn _init_l_Lake_InputFileConfig___fields() -> *mut LeanObject {
    let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
    v___x_505_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig___fields___closed__8),
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig___fields___closed__8_once),
        _init_l_Lake_InputFileConfig___fields___closed__8,
    );
    return v___x_505_;
}
pub unsafe fn l_Lake_InputFileConfig_instConfigFields(
    mut v_name_506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
    v___x_507_ = l_Lake_InputFileConfig___fields;
    return v___x_507_;
}
pub unsafe fn l_Lake_InputFileConfig_instConfigFields___boxed(
    mut v_name_508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_509_: *mut LeanObject = core::ptr::null_mut();
    v_res_509_ = l_Lake_InputFileConfig_instConfigFields(v_name_508_);
    lean_dec(v_name_508_);
    return v_res_509_;
}
pub unsafe fn l_Lake_InputFileConfig_instConfigInfo___lam__0(
    mut v_x1_510_: *mut LeanObject,
    mut v_x2_511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
    v_name_512_ = lean_ctor_get(v_x2_511_, 0);
    lean_inc(v_name_512_);
    v___x_513_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_name_512_,
        v_x2_511_,
        v_x1_510_,
    );
    return v___x_513_;
}
pub unsafe fn _init_l_Lake_InputFileConfig_instConfigInfo___closed__0() -> *mut LeanObject {
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
    v___x_514_ = l_Lake_InputFileConfig___fields;
    v___x_515_ = lean_array_get_size(v___x_514_);
    return v___x_515_;
}
pub unsafe fn _init_l_Lake_InputFileConfig_instConfigInfo___closed__11() -> u8 {
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: u8 = 0;
    v___x_535_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_InputFileConfig_instConfigInfo___closed__0,
    );
    v___x_536_ = lean_unsigned_to_nat(0);
    v___x_537_ = lean_nat_dec_lt(v___x_536_, v___x_535_);
    return v___x_537_;
}
pub unsafe fn _init_l_Lake_InputFileConfig_instConfigInfo___closed__13() -> u8 {
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_540_: u8 = 0;
    v___x_539_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_InputFileConfig_instConfigInfo___closed__0,
    );
    v___x_540_ = lean_nat_dec_le(v___x_539_, v___x_539_);
    return v___x_540_;
}
pub unsafe fn _init_l_Lake_InputFileConfig_instConfigInfo___closed__14() -> usize {
    let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_542_: usize = 0;
    v___x_541_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_InputFileConfig_instConfigInfo___closed__0,
    );
    v___x_542_ = lean_usize_of_nat(v___x_541_);
    return v___x_542_;
}
pub unsafe fn _init_l_Lake_InputFileConfig_instConfigInfo___closed__15() -> *mut LeanObject {
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_544_: usize = 0;
    let mut v___x_545_: usize = 0;
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    v___x_543_ = lean_box(1);
    v___x_544_ = lean_usize_once(
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig_instConfigInfo___closed__14),
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig_instConfigInfo___closed__14_once),
        _init_l_Lake_InputFileConfig_instConfigInfo___closed__14,
    );
    v___x_545_ = 0usize;
    v___x_546_ = l_Lake_InputFileConfig___fields;
    v___f_547_ = l_Lake_InputFileConfig_instConfigInfo___closed__12;
    v___x_548_ = l_Lake_InputFileConfig_instConfigInfo___closed__10;
    v___x_549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_548_,
        v___f_547_,
        v___x_546_,
        v___x_545_,
        v___x_544_,
        v___x_543_,
    );
    return v___x_549_;
}
pub unsafe fn _init_l_Lake_InputFileConfig_instConfigInfo() -> *mut LeanObject {
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_556_: u8 = 0;
    let mut v___x_557_: u8 = 0;
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_550_ = l_Lake_InputFileConfig___fields;
                v___x_555_ = lean_box(1);
                v___x_556_ = lean_uint8_once(
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
                    v___x_557_ = lean_uint8_once(
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
                            v___x_558_ = lean_obj_once(
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
                        v___x_559_ = lean_obj_once(
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
                v___x_553_ = lean_unsigned_to_nat(1);
                lean_inc(v___y_552_);
                v___x_554_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_554_, 0, v___x_550_);
                lean_ctor_set(v___x_554_, 1, v___y_552_);
                lean_ctor_set(v___x_554_, 2, v___x_553_);
                return v___x_554_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputFileConfig_instEmptyCollection(
    mut v_name_560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_561_: u8 = 0;
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    v___x_561_ = 0;
    v___x_562_ = l_Lean_Name_toString(v_name_560_, v___x_561_);
    v___x_563_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_563_, 0, v___x_562_);
    lean_ctor_set_uint8(
        v___x_563_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_561_,
    );
    return v___x_563_;
}
pub unsafe fn l_Lake_InputDirConfig_path___proj___lam__0(
    mut v_cfg_564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_path_565_: *mut LeanObject = core::ptr::null_mut();
    v_path_565_ = lean_ctor_get(v_cfg_564_, 0);
    lean_inc_ref(v_path_565_);
    return v_path_565_;
}
pub unsafe fn l_Lake_InputDirConfig_path___proj___lam__0___boxed(
    mut v_cfg_566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_567_: *mut LeanObject = core::ptr::null_mut();
    v_res_567_ = l_Lake_InputDirConfig_path___proj___lam__0(v_cfg_566_);
    lean_dec_ref(v_cfg_566_);
    return v_res_567_;
}
pub unsafe fn l_Lake_InputDirConfig_path___proj___lam__1(
    mut v_val_568_: *mut LeanObject,
    mut v_cfg_569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_text_570_: u8 = 0;
    let mut v_filter_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_574_: u8 = 0;
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_578_: u8 = 0;
    let mut v_unused_579_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_text_570_ = lean_ctor_get_uint8(
                    v_cfg_569_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_filter_571_ = lean_ctor_get(v_cfg_569_, 1);
                v_isSharedCheck_578_ = (!lean_is_exclusive(v_cfg_569_)) as u8;
                if v_isSharedCheck_578_ == 0 {
                    v_unused_579_ = lean_ctor_get(v_cfg_569_, 0);
                    lean_dec(v_unused_579_);
                    v___x_573_ = v_cfg_569_;
                    v_isShared_574_ = v_isSharedCheck_578_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_filter_571_);
                    lean_dec(v_cfg_569_);
                    v___x_573_ = lean_box(0);
                    v_isShared_574_ = v_isSharedCheck_578_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_574_ == 0 {
                    lean_ctor_set(v___x_573_, 0, v_val_568_);
                    v___x_576_ = v___x_573_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_577_, 0, v_val_568_);
                    lean_ctor_set(v_reuseFailAlloc_577_, 1, v_filter_571_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_577_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_f_580_: *mut LeanObject,
    mut v_cfg_581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_path_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_583_: u8 = 0;
    let mut v_filter_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_587_: u8 = 0;
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_592_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_path_582_ = lean_ctor_get(v_cfg_581_, 0);
                v_text_583_ = lean_ctor_get_uint8(
                    v_cfg_581_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_filter_584_ = lean_ctor_get(v_cfg_581_, 1);
                v_isSharedCheck_592_ = (!lean_is_exclusive(v_cfg_581_)) as u8;
                if v_isSharedCheck_592_ == 0 {
                    v___x_586_ = v_cfg_581_;
                    v_isShared_587_ = v_isSharedCheck_592_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_filter_584_);
                    lean_inc(v_path_582_);
                    lean_dec(v_cfg_581_);
                    v___x_586_ = lean_box(0);
                    v_isShared_587_ = v_isSharedCheck_592_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_588_ = lean_apply_1(v_f_580_, v_path_582_);
                if v_isShared_587_ == 0 {
                    lean_ctor_set(v___x_586_, 0, v___x_588_);
                    v___x_590_ = v___x_586_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
                    lean_ctor_set(v_reuseFailAlloc_591_, 1, v_filter_584_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_591_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_name_593_: *mut LeanObject,
    mut v_x_594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_595_: u8 = 0;
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    v___x_595_ = 0;
    v___x_596_ = l_Lean_Name_toString(v_name_593_, v___x_595_);
    return v___x_596_;
}
pub unsafe fn l_Lake_InputDirConfig_path___proj___lam__3___boxed(
    mut v_name_597_: *mut LeanObject,
    mut v_x_598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_599_: *mut LeanObject = core::ptr::null_mut();
    v_res_599_ = l_Lake_InputDirConfig_path___proj___lam__3(v_name_597_, v_x_598_);
    lean_dec_ref(v_x_598_);
    return v_res_599_;
}
pub unsafe fn l_Lake_InputDirConfig_path___proj(
    mut v_name_603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    v___f_604_ = l_Lake_InputDirConfig_path___proj___closed__0;
    v___f_605_ = l_Lake_InputDirConfig_path___proj___closed__1;
    v___f_606_ = l_Lake_InputDirConfig_path___proj___closed__2;
    v___f_607_ = lean_alloc_closure(
        l_Lake_InputDirConfig_path___proj___lam__3___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_607_, 0, v_name_603_);
    v___x_608_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_608_, 0, v___f_604_);
    lean_ctor_set(v___x_608_, 1, v___f_605_);
    lean_ctor_set(v___x_608_, 2, v___f_606_);
    lean_ctor_set(v___x_608_, 3, v___f_607_);
    return v___x_608_;
}
pub unsafe fn l_Lake_InputDirConfig_path_instConfigField(
    mut v_name_609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    v___x_610_ = l_Lake_InputDirConfig_path___proj(v_name_609_);
    return v___x_610_;
}
pub unsafe fn l_Lake_InputDirConfig_text___proj___lam__0(mut v_cfg_611_: *mut LeanObject) -> u8 {
    let mut v_text_612_: u8 = 0;
    v_text_612_ = lean_ctor_get_uint8(
        v_cfg_611_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    return v_text_612_;
}
pub unsafe fn l_Lake_InputDirConfig_text___proj___lam__0___boxed(
    mut v_cfg_613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_614_: u8 = 0;
    let mut v_r_615_: *mut LeanObject = core::ptr::null_mut();
    v_res_614_ = l_Lake_InputDirConfig_text___proj___lam__0(v_cfg_613_);
    lean_dec_ref(v_cfg_613_);
    v_r_615_ = lean_box((v_res_614_) as usize);
    return v_r_615_;
}
pub unsafe fn l_Lake_InputDirConfig_text___proj___lam__1(
    mut v_val_616_: u8,
    mut v_cfg_617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_path_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_filter_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_622_: u8 = 0;
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_626_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_path_618_ = lean_ctor_get(v_cfg_617_, 0);
                v_filter_619_ = lean_ctor_get(v_cfg_617_, 1);
                v_isSharedCheck_626_ = (!lean_is_exclusive(v_cfg_617_)) as u8;
                if v_isSharedCheck_626_ == 0 {
                    v___x_621_ = v_cfg_617_;
                    v_isShared_622_ = v_isSharedCheck_626_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_filter_619_);
                    lean_inc(v_path_618_);
                    lean_dec(v_cfg_617_);
                    v___x_621_ = lean_box(0);
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
                    v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_625_, 0, v_path_618_);
                    lean_ctor_set(v_reuseFailAlloc_625_, 1, v_filter_619_);
                    v___x_624_ = v_reuseFailAlloc_625_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_624_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_val_616_,
                );
                return v___x_624_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputDirConfig_text___proj___lam__1___boxed(
    mut v_val_627_: *mut LeanObject,
    mut v_cfg_628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_44__boxed_629_: u8 = 0;
    let mut v_res_630_: *mut LeanObject = core::ptr::null_mut();
    v_val_44__boxed_629_ = (lean_unbox(v_val_627_) as u8);
    v_res_630_ = l_Lake_InputDirConfig_text___proj___lam__1(v_val_44__boxed_629_, v_cfg_628_);
    return v_res_630_;
}
pub unsafe fn l_Lake_InputDirConfig_text___proj___lam__2(
    mut v_f_631_: *mut LeanObject,
    mut v_cfg_632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_path_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_634_: u8 = 0;
    let mut v_filter_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_638_: u8 = 0;
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: u8 = 0;
    let mut v_reuseFailAlloc_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_645_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_path_633_ = lean_ctor_get(v_cfg_632_, 0);
                v_text_634_ = lean_ctor_get_uint8(
                    v_cfg_632_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_filter_635_ = lean_ctor_get(v_cfg_632_, 1);
                v_isSharedCheck_645_ = (!lean_is_exclusive(v_cfg_632_)) as u8;
                if v_isSharedCheck_645_ == 0 {
                    v___x_637_ = v_cfg_632_;
                    v_isShared_638_ = v_isSharedCheck_645_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_filter_635_);
                    lean_inc(v_path_633_);
                    lean_dec(v_cfg_632_);
                    v___x_637_ = lean_box(0);
                    v_isShared_638_ = v_isSharedCheck_645_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_639_ = lean_box((v_text_634_) as usize);
                v___x_640_ = lean_apply_1(v_f_631_, v___x_639_);
                if v_isShared_638_ == 0 {
                    v___x_642_ = v___x_637_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_644_, 0, v_path_633_);
                    lean_ctor_set(v_reuseFailAlloc_644_, 1, v_filter_635_);
                    v___x_642_ = v_reuseFailAlloc_644_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_643_ = (lean_unbox(v___x_640_) as u8);
                lean_ctor_set_uint8(
                    v___x_642_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_643_,
                );
                return v___x_642_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputDirConfig_text___proj___lam__3(mut v_x_646_: *mut LeanObject) -> u8 {
    let mut v___x_647_: u8 = 0;
    v___x_647_ = 0;
    return v___x_647_;
}
pub unsafe fn l_Lake_InputDirConfig_text___proj___lam__3___boxed(
    mut v_x_648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_649_: u8 = 0;
    let mut v_r_650_: *mut LeanObject = core::ptr::null_mut();
    v_res_649_ = l_Lake_InputDirConfig_text___proj___lam__3(v_x_648_);
    lean_dec_ref(v_x_648_);
    v_r_650_ = lean_box((v_res_649_) as usize);
    return v_r_650_;
}
pub unsafe fn l_Lake_InputDirConfig_text___proj(
    mut v_name_660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    v___x_661_ = l_Lake_InputDirConfig_text___proj___closed__4;
    return v___x_661_;
}
pub unsafe fn l_Lake_InputDirConfig_text___proj___boxed(
    mut v_name_662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_663_: *mut LeanObject = core::ptr::null_mut();
    v_res_663_ = l_Lake_InputDirConfig_text___proj(v_name_662_);
    lean_dec(v_name_662_);
    return v_res_663_;
}
pub unsafe fn l_Lake_InputDirConfig_text_instConfigField(
    mut v_name_664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    v___x_665_ = l_Lake_InputDirConfig_text___proj(v_name_664_);
    return v___x_665_;
}
pub unsafe fn l_Lake_InputDirConfig_text_instConfigField___boxed(
    mut v_name_666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_667_: *mut LeanObject = core::ptr::null_mut();
    v_res_667_ = l_Lake_InputDirConfig_text_instConfigField(v_name_666_);
    lean_dec(v_name_666_);
    return v_res_667_;
}
pub unsafe fn l_Lake_InputDirConfig_filter___proj___lam__0(
    mut v_cfg_668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_filter_669_: *mut LeanObject = core::ptr::null_mut();
    v_filter_669_ = lean_ctor_get(v_cfg_668_, 1);
    lean_inc_ref(v_filter_669_);
    return v_filter_669_;
}
pub unsafe fn l_Lake_InputDirConfig_filter___proj___lam__0___boxed(
    mut v_cfg_670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_671_: *mut LeanObject = core::ptr::null_mut();
    v_res_671_ = l_Lake_InputDirConfig_filter___proj___lam__0(v_cfg_670_);
    lean_dec_ref(v_cfg_670_);
    return v_res_671_;
}
pub unsafe fn l_Lake_InputDirConfig_filter___proj___lam__1(
    mut v_val_672_: *mut LeanObject,
    mut v_cfg_673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_path_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_675_: u8 = 0;
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_678_: u8 = 0;
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_682_: u8 = 0;
    let mut v_unused_683_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_path_674_ = lean_ctor_get(v_cfg_673_, 0);
                v_text_675_ = lean_ctor_get_uint8(
                    v_cfg_673_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_682_ = (!lean_is_exclusive(v_cfg_673_)) as u8;
                if v_isSharedCheck_682_ == 0 {
                    v_unused_683_ = lean_ctor_get(v_cfg_673_, 1);
                    lean_dec(v_unused_683_);
                    v___x_677_ = v_cfg_673_;
                    v_isShared_678_ = v_isSharedCheck_682_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_path_674_);
                    lean_dec(v_cfg_673_);
                    v___x_677_ = lean_box(0);
                    v_isShared_678_ = v_isSharedCheck_682_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_678_ == 0 {
                    lean_ctor_set(v___x_677_, 1, v_val_672_);
                    v___x_680_ = v___x_677_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_681_, 0, v_path_674_);
                    lean_ctor_set(v_reuseFailAlloc_681_, 1, v_val_672_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_681_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_f_684_: *mut LeanObject,
    mut v_cfg_685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_path_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_687_: u8 = 0;
    let mut v_filter_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_691_: u8 = 0;
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_696_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_path_686_ = lean_ctor_get(v_cfg_685_, 0);
                v_text_687_ = lean_ctor_get_uint8(
                    v_cfg_685_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_filter_688_ = lean_ctor_get(v_cfg_685_, 1);
                v_isSharedCheck_696_ = (!lean_is_exclusive(v_cfg_685_)) as u8;
                if v_isSharedCheck_696_ == 0 {
                    v___x_690_ = v_cfg_685_;
                    v_isShared_691_ = v_isSharedCheck_696_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_filter_688_);
                    lean_inc(v_path_686_);
                    lean_dec(v_cfg_685_);
                    v___x_690_ = lean_box(0);
                    v_isShared_691_ = v_isSharedCheck_696_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_692_ = lean_apply_1(v_f_684_, v_filter_688_);
                if v_isShared_691_ == 0 {
                    lean_ctor_set(v___x_690_, 1, v___x_692_);
                    v___x_694_ = v___x_690_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_695_, 0, v_path_686_);
                    lean_ctor_set(v_reuseFailAlloc_695_, 1, v___x_692_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_695_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
pub unsafe fn _init_l_Lake_InputDirConfig_filter___proj___lam__3___closed__0() -> *mut LeanObject {
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    v___x_697_ = l_Lake_Pattern_star(lean_box(0), lean_box(0));
    return v___x_697_;
}
pub unsafe fn l_Lake_InputDirConfig_filter___proj___lam__3(
    mut v_x_698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    v___x_699_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_filter___proj___lam__3___closed__0),
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_filter___proj___lam__3___closed__0_once),
        _init_l_Lake_InputDirConfig_filter___proj___lam__3___closed__0,
    );
    return v___x_699_;
}
pub unsafe fn l_Lake_InputDirConfig_filter___proj___lam__3___boxed(
    mut v_x_700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_701_: *mut LeanObject = core::ptr::null_mut();
    v_res_701_ = l_Lake_InputDirConfig_filter___proj___lam__3(v_x_700_);
    lean_dec_ref(v_x_700_);
    return v_res_701_;
}
pub unsafe fn l_Lake_InputDirConfig_filter___proj(
    mut v_name_711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    v___x_712_ = l_Lake_InputDirConfig_filter___proj___closed__4;
    return v___x_712_;
}
pub unsafe fn l_Lake_InputDirConfig_filter___proj___boxed(
    mut v_name_713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_714_: *mut LeanObject = core::ptr::null_mut();
    v_res_714_ = l_Lake_InputDirConfig_filter___proj(v_name_713_);
    lean_dec(v_name_713_);
    return v_res_714_;
}
pub unsafe fn l_Lake_InputDirConfig_filter_instConfigField(
    mut v_name_715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    v___x_716_ = l_Lake_InputDirConfig_filter___proj(v_name_715_);
    return v___x_716_;
}
pub unsafe fn l_Lake_InputDirConfig_filter_instConfigField___boxed(
    mut v_name_717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_718_: *mut LeanObject = core::ptr::null_mut();
    v_res_718_ = l_Lake_InputDirConfig_filter_instConfigField(v_name_717_);
    lean_dec(v_name_717_);
    return v_res_718_;
}
pub unsafe fn _init_l_Lake_InputDirConfig___fields___closed__3() -> *mut LeanObject {
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    v___x_726_ = l_Lake_InputDirConfig___fields___closed__2;
    v___x_727_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig___fields___closed__8),
        core::ptr::addr_of_mut!(l_Lake_InputFileConfig___fields___closed__8_once),
        _init_l_Lake_InputFileConfig___fields___closed__8,
    );
    v___x_728_ = lean_array_push(v___x_727_, v___x_726_);
    return v___x_728_;
}
pub unsafe fn _init_l_Lake_InputDirConfig___fields() -> *mut LeanObject {
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    v___x_729_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig___fields___closed__3),
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig___fields___closed__3_once),
        _init_l_Lake_InputDirConfig___fields___closed__3,
    );
    return v___x_729_;
}
pub unsafe fn l_Lake_InputDirConfig_instConfigFields(
    mut v_name_730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    v___x_731_ = l_Lake_InputDirConfig___fields;
    return v___x_731_;
}
pub unsafe fn l_Lake_InputDirConfig_instConfigFields___boxed(
    mut v_name_732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_733_: *mut LeanObject = core::ptr::null_mut();
    v_res_733_ = l_Lake_InputDirConfig_instConfigFields(v_name_732_);
    lean_dec(v_name_732_);
    return v_res_733_;
}
pub unsafe fn _init_l_Lake_InputDirConfig_instConfigInfo___closed__0() -> *mut LeanObject {
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    v___x_734_ = l_Lake_InputDirConfig___fields;
    v___x_735_ = lean_array_get_size(v___x_734_);
    return v___x_735_;
}
pub unsafe fn _init_l_Lake_InputDirConfig_instConfigInfo___closed__1() -> u8 {
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: u8 = 0;
    v___x_736_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_InputDirConfig_instConfigInfo___closed__0,
    );
    v___x_737_ = lean_unsigned_to_nat(0);
    v___x_738_ = lean_nat_dec_lt(v___x_737_, v___x_736_);
    return v___x_738_;
}
pub unsafe fn _init_l_Lake_InputDirConfig_instConfigInfo___closed__2() -> u8 {
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_740_: u8 = 0;
    v___x_739_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_InputDirConfig_instConfigInfo___closed__0,
    );
    v___x_740_ = lean_nat_dec_le(v___x_739_, v___x_739_);
    return v___x_740_;
}
pub unsafe fn _init_l_Lake_InputDirConfig_instConfigInfo___closed__3() -> usize {
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_742_: usize = 0;
    v___x_741_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_InputDirConfig_instConfigInfo___closed__0,
    );
    v___x_742_ = lean_usize_of_nat(v___x_741_);
    return v___x_742_;
}
pub unsafe fn _init_l_Lake_InputDirConfig_instConfigInfo___closed__4() -> *mut LeanObject {
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_744_: usize = 0;
    let mut v___x_745_: usize = 0;
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    v___x_743_ = lean_box(1);
    v___x_744_ = lean_usize_once(
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_instConfigInfo___closed__3),
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_instConfigInfo___closed__3_once),
        _init_l_Lake_InputDirConfig_instConfigInfo___closed__3,
    );
    v___x_745_ = 0usize;
    v___x_746_ = l_Lake_InputDirConfig___fields;
    v___f_747_ = l_Lake_InputFileConfig_instConfigInfo___closed__12;
    v___x_748_ = l_Lake_InputFileConfig_instConfigInfo___closed__10;
    v___x_749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_748_,
        v___f_747_,
        v___x_746_,
        v___x_745_,
        v___x_744_,
        v___x_743_,
    );
    return v___x_749_;
}
pub unsafe fn _init_l_Lake_InputDirConfig_instConfigInfo() -> *mut LeanObject {
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: u8 = 0;
    let mut v___x_757_: u8 = 0;
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_750_ = l_Lake_InputDirConfig___fields;
                v___x_755_ = lean_box(1);
                v___x_756_ = lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Lake_InputDirConfig_instConfigInfo___closed__1),
                    core::ptr::addr_of_mut!(l_Lake_InputDirConfig_instConfigInfo___closed__1_once),
                    _init_l_Lake_InputDirConfig_instConfigInfo___closed__1,
                );
                if v___x_756_ == 0 {
                    v___y_752_ = v___x_755_;
                    state = 1;
                    continue;
                } else {
                    v___x_757_ = lean_uint8_once(
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
                            v___x_758_ = lean_obj_once(
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
                        v___x_759_ = lean_obj_once(
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
                v___x_753_ = lean_unsigned_to_nat(1);
                lean_inc(v___y_752_);
                v___x_754_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_754_, 0, v___x_750_);
                lean_ctor_set(v___x_754_, 1, v___y_752_);
                lean_ctor_set(v___x_754_, 2, v___x_753_);
                return v___x_754_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_InputDirConfig_instEmptyCollection(
    mut v_name_760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_761_: u8 = 0;
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    v___x_761_ = 0;
    v___x_762_ = l_Lean_Name_toString(v_name_760_, v___x_761_);
    v___x_763_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_filter___proj___lam__3___closed__0),
        core::ptr::addr_of_mut!(l_Lake_InputDirConfig_filter___proj___lam__3___closed__0_once),
        _init_l_Lake_InputDirConfig_filter___proj___lam__3___closed__0,
    );
    v___x_764_ = lean_alloc_ctor(0, 2, (1) as u32);
    lean_ctor_set(v___x_764_, 0, v___x_762_);
    lean_ctor_set(v___x_764_, 1, v___x_763_);
    lean_ctor_set_uint8(
        v___x_764_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v___x_761_,
    );
    return v___x_764_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_InputFileConfig(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Pattern(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_MetaClasses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_InputFileConfig___fields = _init_l_Lake_InputFileConfig___fields();
    lean_mark_persistent(l_Lake_InputFileConfig___fields);
    l_Lake_InputFileConfig_instConfigInfo = _init_l_Lake_InputFileConfig_instConfigInfo();
    lean_mark_persistent(l_Lake_InputFileConfig_instConfigInfo);
    l_Lake_InputDirConfig___fields = _init_l_Lake_InputDirConfig___fields();
    lean_mark_persistent(l_Lake_InputDirConfig___fields);
    l_Lake_InputDirConfig_instConfigInfo = _init_l_Lake_InputDirConfig_instConfigInfo();
    lean_mark_persistent(l_Lake_InputDirConfig_instConfigInfo);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_InputFileConfig(builtin: u8) -> *mut LeanObject {
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
pub unsafe fn initialize_Lake_Config_InputFileConfig(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Pattern(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_MetaClasses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_InputFileConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Config_InputFileConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Config_InputFileConfig(builtin);
}
