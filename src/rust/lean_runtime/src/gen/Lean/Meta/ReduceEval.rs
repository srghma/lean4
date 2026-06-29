// Lean compiler output
// Module: Lean.Meta.ReduceEval
// Imports: Lean.Meta.Offset
use crate::r#gen::Init::Prelude::{l_Lean_Name_num___override, l_Lean_Name_str___override};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_constName_x3f, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_getRevArg_x21, l_Lean_Expr_isAppOf,
    l_Lean_Expr_isAppOfArity,
};
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_TransparencyMode_toUInt64,
};
use crate::r#gen::Lean::Meta::Offset::{
    initialize_Lean_Meta_Offset, l_Lean_Meta_evalNat, runtime_initialize_Lean_Meta_Offset,
};
use crate::r#gen::Lean::Meta::TransparencyMode::l_Lean_Meta_TransparencyMode_lt;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_mod, lean_nat_pow, lean_nat_sub,
    lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_whnf;
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__0_value: crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [114, 101, 100, 117, 99, 101, 69, 118, 97, 108, 58, 32, 102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 101, 118, 97, 108, 117, 97, 116, 101, 32, 97, 114, 103, 117, 109, 101, 110, 116, 0]};
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_instReduceEvalNat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReduceEvalNat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReduceEvalNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instReduceEvalNat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [79, 112, 116, 105, 111, 110, 0],
};
static mut l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__1_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [115, 111, 109, 101, 0],
};
static mut l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        18184376426117065311 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        4893146552088433753 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__3_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 111, 110, 101, 0],
};
static mut l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        18184376426117065311 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        9480010471355609749 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReduceEvalString___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReduceEvalString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instReduceEvalString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [78, 97, 109, 101, 0],
};
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [110, 117, 109, 0],
};
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        13306843946249674491 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        7229350633979142691 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [115, 116, 114, 0],
};
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        13306843946249674491 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        8392322758047580095 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__6_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [97, 110, 111, 110, 121, 109, 111, 117, 115, 0],
};
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        13306843946249674491 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        8742792063936078747 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalName___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReduceEvalName___private__1___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReduceEvalName___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalName___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instReduceEvalName: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalName___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 105, 115, 116, 0],
};
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__1_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [110, 105, 108, 0],
};
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__2_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [99, 111, 110, 115, 0],
};
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [70, 105, 110, 0],
};
static mut l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__1_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [109, 107, 0],
};
static mut l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15815496672699636542 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        5825593324384481310 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalBitVec___private__1___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [66, 105, 116, 86, 101, 99, 0],
};
static mut l_Lean_Meta_instReduceEvalBitVec___private__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBitVec___private__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalBitVec___private__1___closed__1_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [111, 102, 70, 105, 110, 0],
};
static mut l_Lean_Meta_instReduceEvalBitVec___private__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBitVec___private__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_instReduceEvalBitVec___private__1___closed__2_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBitVec___private__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        5394957827732845164 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_instReduceEvalBitVec___private__1___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBitVec___private__1___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBitVec___private__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        3686919969481140037 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReduceEvalBitVec___private__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBitVec___private__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalBool___private__1___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [66, 111, 111, 108, 0],
};
static mut l_Lean_Meta_instReduceEvalBool___private__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___private__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalBool___private__1___closed__1_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_instReduceEvalBool___private__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___private__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_instReduceEvalBool___private__1___closed__2_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___private__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        12882480457794858234 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_instReduceEvalBool___private__1___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___private__1___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___private__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        9255189395584251158 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReduceEvalBool___private__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___private__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalBool___private__1___closed__3_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_instReduceEvalBool___private__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___private__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_instReduceEvalBool___private__1___closed__4_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___private__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        12882480457794858234 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_instReduceEvalBool___private__1___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___private__1___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___private__1___closed__3_value)
            as *mut crate::leanh::LeanObject,
        15761733860085307253 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReduceEvalBool___private__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___private__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalBool___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReduceEvalBool___private__1___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReduceEvalBool___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instReduceEvalBool: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__0_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [66, 105, 110, 100, 101, 114, 73, 110, 102, 111, 0],
};
static mut l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__1_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [100, 101, 102, 97, 117, 108, 116, 0],
};
static mut l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__2_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [105, 109, 112, 108, 105, 99, 105, 116, 0],
};
static mut l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__3_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
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
        115, 116, 114, 105, 99, 116, 73, 109, 112, 108, 105, 99, 105, 116, 0,
    ],
};
static mut l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__4_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [105, 110, 115, 116, 73, 109, 112, 108, 105, 99, 105, 116, 0],
};
static mut l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalBinderInfo___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Meta_instReduceEvalBinderInfo___private__1___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_instReduceEvalBinderInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBinderInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instReduceEvalBinderInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBinderInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalLiteral___private__1___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [76, 105, 116, 101, 114, 97, 108, 0],
};
static mut l_Lean_Meta_instReduceEvalLiteral___private__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalLiteral___private__1___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [110, 97, 116, 86, 97, 108, 0],
};
static mut l_Lean_Meta_instReduceEvalLiteral___private__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7001815944269665831 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        9295767770006931264 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalLiteral___private__1___closed__3_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [115, 116, 114, 86, 97, 108, 0],
};
static mut l_Lean_Meta_instReduceEvalLiteral___private__1___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7001815944269665831 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__3_value)
            as *mut crate::leanh::LeanObject,
        2005404019190257220 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalLiteral___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReduceEvalLiteral___private__1___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReduceEvalLiteral___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instReduceEvalLiteral: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalMVarId___private__1___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [77, 86, 97, 114, 73, 100, 0],
};
static mut l_Lean_Meta_instReduceEvalMVarId___private__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalMVarId___private__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalMVarId___private__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        5356933541775719089 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        10225135193421524061 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalMVarId___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReduceEvalMVarId___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReduceEvalMVarId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalMVarId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instReduceEvalMVarId: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalMVarId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__0_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [76, 101, 118, 101, 108, 77, 86, 97, 114, 73, 100, 0],
};
static mut l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        10629041231479782489 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        16867186451750755797 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalLevelMVarId___closed__0_value:
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
    m_fun: l_Lean_Meta_instReduceEvalLevelMVarId___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_instReduceEvalLevelMVarId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLevelMVarId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instReduceEvalLevelMVarId: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLevelMVarId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalFVarId___private__1___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [70, 86, 97, 114, 73, 100, 0],
};
static mut l_Lean_Meta_instReduceEvalFVarId___private__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalFVarId___private__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalFVarId___private__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        6212595679582900358 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        6968149084986791158 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReduceEvalFVarId___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReduceEvalFVarId___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReduceEvalFVarId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalFVarId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instReduceEvalFVarId: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalFVarId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_reduceEval___redArg(
    mut v_inst_1737_: *mut crate::leanh::LeanObject,
    mut v_e_1738_: *mut crate::leanh::LeanObject,
    mut v_a_1739_: *mut crate::leanh::LeanObject,
    mut v_a_1740_: *mut crate::leanh::LeanObject,
    mut v_a_1741_: *mut crate::leanh::LeanObject,
    mut v_a_1742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1745_: u8 = 0;
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_1747_: u8 = 0;
    let mut v_ctxApprox_1748_: u8 = 0;
    let mut v_quasiPatternApprox_1749_: u8 = 0;
    let mut v_constApprox_1750_: u8 = 0;
    let mut v_isDefEqStuckEx_1751_: u8 = 0;
    let mut v_unificationHints_1752_: u8 = 0;
    let mut v_proofIrrelevance_1753_: u8 = 0;
    let mut v_assignSyntheticOpaque_1754_: u8 = 0;
    let mut v_offsetCnstrs_1755_: u8 = 0;
    let mut v_etaStruct_1756_: u8 = 0;
    let mut v_univApprox_1757_: u8 = 0;
    let mut v_iota_1758_: u8 = 0;
    let mut v_beta_1759_: u8 = 0;
    let mut v_proj_1760_: u8 = 0;
    let mut v_zeta_1761_: u8 = 0;
    let mut v_zetaDelta_1762_: u8 = 0;
    let mut v_zetaUnused_1763_: u8 = 0;
    let mut v_zetaHave_1764_: u8 = 0;
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1767_: u8 = 0;
    let mut v_trackZetaDelta_1768_: u8 = 0;
    let mut v_zetaDeltaSet_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_1775_: u8 = 0;
    let mut v_inTypeClassResolution_1776_: u8 = 0;
    let mut v_cacheInferType_1777_: u8 = 0;
    let mut v_config_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: u64 = 0;
    let mut v___x_1781_: u64 = 0;
    let mut v___x_1782_: u64 = 0;
    let mut v___x_1783_: u64 = 0;
    let mut v___x_1784_: u64 = 0;
    let mut v_key_1785_: u64 = 0;
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1790_: u8 = 0;
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transparency_1792_: u8 = 0;
    let mut v___x_1793_: u8 = 0;
    let mut v___x_1794_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1791_ = l_Lean_Meta_Context_config(v_a_1739_);
                v_transparency_1792_ = crate::leanh::lean_ctor_get_uint8(v___x_1791_, 9 as u32);
                crate::leanh::lean_dec_ref(v___x_1791_);
                v___x_1793_ = 1;
                v___x_1794_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1792_, v___x_1793_);
                if v___x_1794_ == 0 {
                    v___y_1745_ = v_transparency_1792_;
                    state = 1;
                    continue;
                } else {
                    v___y_1745_ = v___x_1793_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1746_ = l_Lean_Meta_Context_config(v_a_1739_);
                v_foApprox_1747_ = crate::leanh::lean_ctor_get_uint8(v___x_1746_, 0 as u32);
                v_ctxApprox_1748_ = crate::leanh::lean_ctor_get_uint8(v___x_1746_, 1 as u32);
                v_quasiPatternApprox_1749_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_1746_, 2 as u32);
                v_constApprox_1750_ = crate::leanh::lean_ctor_get_uint8(v___x_1746_, 3 as u32);
                v_isDefEqStuckEx_1751_ = crate::leanh::lean_ctor_get_uint8(v___x_1746_, 4 as u32);
                v_unificationHints_1752_ = crate::leanh::lean_ctor_get_uint8(v___x_1746_, 5 as u32);
                v_proofIrrelevance_1753_ = crate::leanh::lean_ctor_get_uint8(v___x_1746_, 6 as u32);
                v_assignSyntheticOpaque_1754_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_1746_, 7 as u32);
                v_offsetCnstrs_1755_ = crate::leanh::lean_ctor_get_uint8(v___x_1746_, 8 as u32);
                v_etaStruct_1756_ = crate::leanh::lean_ctor_get_uint8(v___x_1746_, 10 as u32);
                v_univApprox_1757_ = crate::leanh::lean_ctor_get_uint8(v___x_1746_, 11 as u32);
                v_iota_1758_ = crate::leanh::lean_ctor_get_uint8(v___x_1746_, 12 as u32);
                v_beta_1759_ = crate::leanh::lean_ctor_get_uint8(v___x_1746_, 13 as u32);
                v_proj_1760_ = crate::leanh::lean_ctor_get_uint8(v___x_1746_, 14 as u32);
                v_zeta_1761_ = crate::leanh::lean_ctor_get_uint8(v___x_1746_, 15 as u32);
                v_zetaDelta_1762_ = crate::leanh::lean_ctor_get_uint8(v___x_1746_, 16 as u32);
                v_zetaUnused_1763_ = crate::leanh::lean_ctor_get_uint8(v___x_1746_, 17 as u32);
                v_zetaHave_1764_ = crate::leanh::lean_ctor_get_uint8(v___x_1746_, 18 as u32);
                v_isSharedCheck_1790_ = (!crate::leanh::lean_is_exclusive(v___x_1746_)) as u8;
                if v_isSharedCheck_1790_ == 0 {
                    v___x_1766_ = v___x_1746_;
                    v_isShared_1767_ = v_isSharedCheck_1790_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_1746_);
                    v___x_1766_ = crate::leanh::lean_box(0);
                    v_isShared_1767_ = v_isSharedCheck_1790_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_trackZetaDelta_1768_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1739_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_1769_ = crate::leanh::lean_ctor_get(v_a_1739_, 1);
                v_lctx_1770_ = crate::leanh::lean_ctor_get(v_a_1739_, 2);
                v_localInstances_1771_ = crate::leanh::lean_ctor_get(v_a_1739_, 3);
                v_defEqCtx_x3f_1772_ = crate::leanh::lean_ctor_get(v_a_1739_, 4);
                v_synthPendingDepth_1773_ = crate::leanh::lean_ctor_get(v_a_1739_, 5);
                v_canUnfold_x3f_1774_ = crate::leanh::lean_ctor_get(v_a_1739_, 6);
                v_univApprox_1775_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1739_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_1776_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1739_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_1777_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1739_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_1767_ == 0 {
                    v_config_1779_ = v___x_1766_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1789_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1789_,
                        0 as u32,
                        v_foApprox_1747_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1789_,
                        1 as u32,
                        v_ctxApprox_1748_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1789_,
                        2 as u32,
                        v_quasiPatternApprox_1749_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1789_,
                        3 as u32,
                        v_constApprox_1750_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1789_,
                        4 as u32,
                        v_isDefEqStuckEx_1751_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1789_,
                        5 as u32,
                        v_unificationHints_1752_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1789_,
                        6 as u32,
                        v_proofIrrelevance_1753_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1789_,
                        7 as u32,
                        v_assignSyntheticOpaque_1754_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1789_,
                        8 as u32,
                        v_offsetCnstrs_1755_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1789_,
                        10 as u32,
                        v_etaStruct_1756_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1789_,
                        11 as u32,
                        v_univApprox_1757_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1789_,
                        12 as u32,
                        v_iota_1758_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1789_,
                        13 as u32,
                        v_beta_1759_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1789_,
                        14 as u32,
                        v_proj_1760_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1789_,
                        15 as u32,
                        v_zeta_1761_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1789_,
                        16 as u32,
                        v_zetaDelta_1762_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1789_,
                        17 as u32,
                        v_zetaUnused_1763_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1789_,
                        18 as u32,
                        v_zetaHave_1764_,
                    );
                    v_config_1779_ = v_reuseFailAlloc_1789_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(v_config_1779_, 9 as u32, v___y_1745_);
                v___x_1780_ = l_Lean_Meta_Context_configKey(v_a_1739_);
                v___x_1781_ = 3u64;
                v___x_1782_ = lean_uint64_shift_right(v___x_1780_, v___x_1781_);
                v___x_1783_ = lean_uint64_shift_left(v___x_1782_, v___x_1781_);
                v___x_1784_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_1745_);
                v_key_1785_ = lean_uint64_lor(v___x_1783_, v___x_1784_);
                v___x_1786_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_1786_, 0, v_config_1779_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_1786_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_1785_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_1774_);
                crate::leanh::lean_inc(v_synthPendingDepth_1773_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_1772_);
                crate::leanh::lean_inc_ref(v_localInstances_1771_);
                crate::leanh::lean_inc_ref(v_lctx_1770_);
                crate::leanh::lean_inc(v_zetaDeltaSet_1769_);
                v___x_1787_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_1787_, 0, v___x_1786_);
                crate::leanh::lean_ctor_set(v___x_1787_, 1, v_zetaDeltaSet_1769_);
                crate::leanh::lean_ctor_set(v___x_1787_, 2, v_lctx_1770_);
                crate::leanh::lean_ctor_set(v___x_1787_, 3, v_localInstances_1771_);
                crate::leanh::lean_ctor_set(v___x_1787_, 4, v_defEqCtx_x3f_1772_);
                crate::leanh::lean_ctor_set(v___x_1787_, 5, v_synthPendingDepth_1773_);
                crate::leanh::lean_ctor_set(v___x_1787_, 6, v_canUnfold_x3f_1774_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1787_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_1768_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1787_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_1775_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1787_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_1776_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1787_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_1777_,
                );
                crate::leanh::lean_inc(v_a_1742_);
                crate::leanh::lean_inc_ref(v_a_1741_);
                crate::leanh::lean_inc(v_a_1740_);
                v___x_1788_ = crate::leanh::lean_apply_6(
                    v_inst_1737_,
                    v_e_1738_,
                    v___x_1787_,
                    v_a_1740_,
                    v_a_1741_,
                    v_a_1742_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1788_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_reduceEval___redArg___boxed(
    mut v_inst_1795_: *mut crate::leanh::LeanObject,
    mut v_e_1796_: *mut crate::leanh::LeanObject,
    mut v_a_1797_: *mut crate::leanh::LeanObject,
    mut v_a_1798_: *mut crate::leanh::LeanObject,
    mut v_a_1799_: *mut crate::leanh::LeanObject,
    mut v_a_1800_: *mut crate::leanh::LeanObject,
    mut v_a_1801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1802_ = l_Lean_Meta_reduceEval___redArg(
        v_inst_1795_,
        v_e_1796_,
        v_a_1797_,
        v_a_1798_,
        v_a_1799_,
        v_a_1800_,
    );
    crate::leanh::lean_dec(v_a_1800_);
    crate::leanh::lean_dec_ref(v_a_1799_);
    crate::leanh::lean_dec(v_a_1798_);
    crate::leanh::lean_dec_ref(v_a_1797_);
    return v_res_1802_;
}
pub unsafe fn l_Lean_Meta_reduceEval(
    mut v_00_u03b1_1803_: *mut crate::leanh::LeanObject,
    mut v_inst_1804_: *mut crate::leanh::LeanObject,
    mut v_e_1805_: *mut crate::leanh::LeanObject,
    mut v_a_1806_: *mut crate::leanh::LeanObject,
    mut v_a_1807_: *mut crate::leanh::LeanObject,
    mut v_a_1808_: *mut crate::leanh::LeanObject,
    mut v_a_1809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1811_ = l_Lean_Meta_reduceEval___redArg(
        v_inst_1804_,
        v_e_1805_,
        v_a_1806_,
        v_a_1807_,
        v_a_1808_,
        v_a_1809_,
    );
    return v___x_1811_;
}
pub unsafe fn l_Lean_Meta_reduceEval___boxed(
    mut v_00_u03b1_1812_: *mut crate::leanh::LeanObject,
    mut v_inst_1813_: *mut crate::leanh::LeanObject,
    mut v_e_1814_: *mut crate::leanh::LeanObject,
    mut v_a_1815_: *mut crate::leanh::LeanObject,
    mut v_a_1816_: *mut crate::leanh::LeanObject,
    mut v_a_1817_: *mut crate::leanh::LeanObject,
    mut v_a_1818_: *mut crate::leanh::LeanObject,
    mut v_a_1819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1820_ = l_Lean_Meta_reduceEval(
        v_00_u03b1_1812_,
        v_inst_1813_,
        v_e_1814_,
        v_a_1815_,
        v_a_1816_,
        v_a_1817_,
        v_a_1818_,
    );
    crate::leanh::lean_dec(v_a_1818_);
    crate::leanh::lean_dec_ref(v_a_1817_);
    crate::leanh::lean_dec(v_a_1816_);
    crate::leanh::lean_dec_ref(v_a_1815_);
    return v_res_1820_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(
    mut v_msgData_1821_: *mut crate::leanh::LeanObject,
    mut v___y_1822_: *mut crate::leanh::LeanObject,
    mut v___y_1823_: *mut crate::leanh::LeanObject,
    mut v___y_1824_: *mut crate::leanh::LeanObject,
    mut v___y_1825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1827_ = lean_st_ref_get(v___y_1825_);
    v_env_1828_ = crate::leanh::lean_ctor_get(v___x_1827_, 0);
    crate::leanh::lean_inc_ref(v_env_1828_);
    crate::leanh::lean_dec(v___x_1827_);
    v___x_1829_ = lean_st_ref_get(v___y_1823_);
    v_mctx_1830_ = crate::leanh::lean_ctor_get(v___x_1829_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1830_);
    crate::leanh::lean_dec(v___x_1829_);
    v_lctx_1831_ = crate::leanh::lean_ctor_get(v___y_1822_, 2);
    v_options_1832_ = crate::leanh::lean_ctor_get(v___y_1824_, 2);
    crate::leanh::lean_inc_ref(v_options_1832_);
    crate::leanh::lean_inc_ref(v_lctx_1831_);
    v___x_1833_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1833_, 0, v_env_1828_);
    crate::leanh::lean_ctor_set(v___x_1833_, 1, v_mctx_1830_);
    crate::leanh::lean_ctor_set(v___x_1833_, 2, v_lctx_1831_);
    crate::leanh::lean_ctor_set(v___x_1833_, 3, v_options_1832_);
    v___x_1834_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1834_, 0, v___x_1833_);
    crate::leanh::lean_ctor_set(v___x_1834_, 1, v_msgData_1821_);
    v___x_1835_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1835_, 0, v___x_1834_);
    return v___x_1835_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0___boxed(
    mut v_msgData_1836_: *mut crate::leanh::LeanObject,
    mut v___y_1837_: *mut crate::leanh::LeanObject,
    mut v___y_1838_: *mut crate::leanh::LeanObject,
    mut v___y_1839_: *mut crate::leanh::LeanObject,
    mut v___y_1840_: *mut crate::leanh::LeanObject,
    mut v___y_1841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1842_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(v_msgData_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
    crate::leanh::lean_dec(v___y_1840_);
    crate::leanh::lean_dec_ref(v___y_1839_);
    crate::leanh::lean_dec(v___y_1838_);
    crate::leanh::lean_dec_ref(v___y_1837_);
    return v_res_1842_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(
    mut v_msg_1843_: *mut crate::leanh::LeanObject,
    mut v___y_1844_: *mut crate::leanh::LeanObject,
    mut v___y_1845_: *mut crate::leanh::LeanObject,
    mut v___y_1846_: *mut crate::leanh::LeanObject,
    mut v___y_1847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1854_: u8 = 0;
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1859_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1849_ = crate::leanh::lean_ctor_get(v___y_1846_, 5);
                v___x_1850_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(v_msg_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
                v_a_1851_ = crate::leanh::lean_ctor_get(v___x_1850_, 0);
                v_isSharedCheck_1859_ = (!crate::leanh::lean_is_exclusive(v___x_1850_)) as u8;
                if v_isSharedCheck_1859_ == 0 {
                    v___x_1853_ = v___x_1850_;
                    v_isShared_1854_ = v_isSharedCheck_1859_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1851_);
                    crate::leanh::lean_dec(v___x_1850_);
                    v___x_1853_ = crate::leanh::lean_box(0);
                    v_isShared_1854_ = v_isSharedCheck_1859_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1849_);
                v___x_1855_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1855_, 0, v_ref_1849_);
                crate::leanh::lean_ctor_set(v___x_1855_, 1, v_a_1851_);
                if v_isShared_1854_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1853_, 1);
                    crate::leanh::lean_ctor_set(v___x_1853_, 0, v___x_1855_);
                    v___x_1857_ = v___x_1853_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1858_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
                    v___x_1857_ = v_reuseFailAlloc_1858_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1857_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg___boxed(
    mut v_msg_1860_: *mut crate::leanh::LeanObject,
    mut v___y_1861_: *mut crate::leanh::LeanObject,
    mut v___y_1862_: *mut crate::leanh::LeanObject,
    mut v___y_1863_: *mut crate::leanh::LeanObject,
    mut v___y_1864_: *mut crate::leanh::LeanObject,
    mut v___y_1865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1866_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(v_msg_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
    crate::leanh::lean_dec(v___y_1864_);
    crate::leanh::lean_dec_ref(v___y_1863_);
    crate::leanh::lean_dec(v___y_1862_);
    crate::leanh::lean_dec_ref(v___y_1861_);
    return v_res_1866_;
}
pub unsafe fn _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1868_ =
        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__0;
    v___x_1869_ = l_Lean_stringToMessageData(v___x_1868_);
    return v___x_1869_;
}
pub unsafe fn l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
    mut v_e_1870_: *mut crate::leanh::LeanObject,
    mut v_a_1871_: *mut crate::leanh::LeanObject,
    mut v_a_1872_: *mut crate::leanh::LeanObject,
    mut v_a_1873_: *mut crate::leanh::LeanObject,
    mut v_a_1874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1876_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1_once), _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1);
    v___x_1877_ = l_Lean_indentExpr(v_e_1870_);
    v___x_1878_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1878_, 0, v___x_1876_);
    crate::leanh::lean_ctor_set(v___x_1878_, 1, v___x_1877_);
    v___x_1879_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(v___x_1878_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
    return v___x_1879_;
}
pub unsafe fn l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___boxed(
    mut v_e_1880_: *mut crate::leanh::LeanObject,
    mut v_a_1881_: *mut crate::leanh::LeanObject,
    mut v_a_1882_: *mut crate::leanh::LeanObject,
    mut v_a_1883_: *mut crate::leanh::LeanObject,
    mut v_a_1884_: *mut crate::leanh::LeanObject,
    mut v_a_1885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1886_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
        v_e_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_,
    );
    crate::leanh::lean_dec(v_a_1884_);
    crate::leanh::lean_dec_ref(v_a_1883_);
    crate::leanh::lean_dec(v_a_1882_);
    crate::leanh::lean_dec_ref(v_a_1881_);
    return v_res_1886_;
}
pub unsafe fn l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(
    mut v_00_u03b1_1887_: *mut crate::leanh::LeanObject,
    mut v_e_1888_: *mut crate::leanh::LeanObject,
    mut v_a_1889_: *mut crate::leanh::LeanObject,
    mut v_a_1890_: *mut crate::leanh::LeanObject,
    mut v_a_1891_: *mut crate::leanh::LeanObject,
    mut v_a_1892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1894_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
        v_e_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_,
    );
    return v___x_1894_;
}
pub unsafe fn l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___boxed(
    mut v_00_u03b1_1895_: *mut crate::leanh::LeanObject,
    mut v_e_1896_: *mut crate::leanh::LeanObject,
    mut v_a_1897_: *mut crate::leanh::LeanObject,
    mut v_a_1898_: *mut crate::leanh::LeanObject,
    mut v_a_1899_: *mut crate::leanh::LeanObject,
    mut v_a_1900_: *mut crate::leanh::LeanObject,
    mut v_a_1901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1902_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(
        v_00_u03b1_1895_,
        v_e_1896_,
        v_a_1897_,
        v_a_1898_,
        v_a_1899_,
        v_a_1900_,
    );
    crate::leanh::lean_dec(v_a_1900_);
    crate::leanh::lean_dec_ref(v_a_1899_);
    crate::leanh::lean_dec(v_a_1898_);
    crate::leanh::lean_dec_ref(v_a_1897_);
    return v_res_1902_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0(
    mut v_00_u03b1_1903_: *mut crate::leanh::LeanObject,
    mut v_msg_1904_: *mut crate::leanh::LeanObject,
    mut v___y_1905_: *mut crate::leanh::LeanObject,
    mut v___y_1906_: *mut crate::leanh::LeanObject,
    mut v___y_1907_: *mut crate::leanh::LeanObject,
    mut v___y_1908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1910_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(v_msg_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
    return v___x_1910_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___boxed(
    mut v_00_u03b1_1911_: *mut crate::leanh::LeanObject,
    mut v_msg_1912_: *mut crate::leanh::LeanObject,
    mut v___y_1913_: *mut crate::leanh::LeanObject,
    mut v___y_1914_: *mut crate::leanh::LeanObject,
    mut v___y_1915_: *mut crate::leanh::LeanObject,
    mut v___y_1916_: *mut crate::leanh::LeanObject,
    mut v___y_1917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1918_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0(v_00_u03b1_1911_, v_msg_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
    crate::leanh::lean_dec(v___y_1916_);
    crate::leanh::lean_dec_ref(v___y_1915_);
    crate::leanh::lean_dec(v___y_1914_);
    crate::leanh::lean_dec_ref(v___y_1913_);
    return v_res_1918_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalNat___private__1(
    mut v_e_1919_: *mut crate::leanh::LeanObject,
    mut v_a_1920_: *mut crate::leanh::LeanObject,
    mut v_a_1921_: *mut crate::leanh::LeanObject,
    mut v_a_1922_: *mut crate::leanh::LeanObject,
    mut v_a_1923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1931_: u8 = 0;
    let mut v_val_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1937_: u8 = 0;
    let mut v_a_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1941_: u8 = 0;
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1945_: u8 = 0;
    let mut v_a_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1949_: u8 = 0;
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1953_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_1923_);
                crate::leanh::lean_inc_ref(v_a_1922_);
                crate::leanh::lean_inc(v_a_1921_);
                crate::leanh::lean_inc_ref(v_a_1920_);
                v___x_1925_ = lean_whnf(v_e_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
                if crate::leanh::lean_obj_tag(v___x_1925_) == 0 {
                    v_a_1926_ = crate::leanh::lean_ctor_get(v___x_1925_, 0);
                    crate::leanh::lean_inc_n(v_a_1926_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1925_, 1);
                    v___x_1927_ =
                        l_Lean_Meta_evalNat(v_a_1926_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
                    if crate::leanh::lean_obj_tag(v___x_1927_) == 0 {
                        v_a_1928_ = crate::leanh::lean_ctor_get(v___x_1927_, 0);
                        v_isSharedCheck_1937_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1927_)) as u8;
                        if v_isSharedCheck_1937_ == 0 {
                            v___x_1930_ = v___x_1927_;
                            v_isShared_1931_ = v_isSharedCheck_1937_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1928_);
                            crate::leanh::lean_dec(v___x_1927_);
                            v___x_1930_ = crate::leanh::lean_box(0);
                            v_isShared_1931_ = v_isSharedCheck_1937_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1926_);
                        v_a_1938_ = crate::leanh::lean_ctor_get(v___x_1927_, 0);
                        v_isSharedCheck_1945_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1927_)) as u8;
                        if v_isSharedCheck_1945_ == 0 {
                            v___x_1940_ = v___x_1927_;
                            v_isShared_1941_ = v_isSharedCheck_1945_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1938_);
                            crate::leanh::lean_dec(v___x_1927_);
                            v___x_1940_ = crate::leanh::lean_box(0);
                            v_isShared_1941_ = v_isSharedCheck_1945_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_1946_ = crate::leanh::lean_ctor_get(v___x_1925_, 0);
                    v_isSharedCheck_1953_ = (!crate::leanh::lean_is_exclusive(v___x_1925_)) as u8;
                    if v_isSharedCheck_1953_ == 0 {
                        v___x_1948_ = v___x_1925_;
                        v_isShared_1949_ = v_isSharedCheck_1953_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1946_);
                        crate::leanh::lean_dec(v___x_1925_);
                        v___x_1948_ = crate::leanh::lean_box(0);
                        v_isShared_1949_ = v_isSharedCheck_1953_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1928_) == 1 {
                    crate::leanh::lean_dec(v_a_1926_);
                    v_val_1932_ = crate::leanh::lean_ctor_get(v_a_1928_, 0);
                    crate::leanh::lean_inc(v_val_1932_);
                    crate::leanh::lean_dec_ref_known(v_a_1928_, 1);
                    if v_isShared_1931_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1930_, 0, v_val_1932_);
                        v___x_1934_ = v___x_1930_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1935_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_val_1932_);
                        v___x_1934_ = v_reuseFailAlloc_1935_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1930_);
                    crate::leanh::lean_dec(v_a_1928_);
                    v___x_1936_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_a_1926_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_,
                        );
                    return v___x_1936_;
                }
            }
            2 => {
                return v___x_1934_;
            }
            3 => {
                if v_isShared_1941_ == 0 {
                    v___x_1943_ = v___x_1940_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1944_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
                    v___x_1943_ = v_reuseFailAlloc_1944_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1943_;
            }
            5 => {
                if v_isShared_1949_ == 0 {
                    v___x_1951_ = v___x_1948_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1952_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
                    v___x_1951_ = v_reuseFailAlloc_1952_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1951_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instReduceEvalNat___private__1___boxed(
    mut v_e_1954_: *mut crate::leanh::LeanObject,
    mut v_a_1955_: *mut crate::leanh::LeanObject,
    mut v_a_1956_: *mut crate::leanh::LeanObject,
    mut v_a_1957_: *mut crate::leanh::LeanObject,
    mut v_a_1958_: *mut crate::leanh::LeanObject,
    mut v_a_1959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1960_ = l_Lean_Meta_instReduceEvalNat___private__1(
        v_e_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_,
    );
    crate::leanh::lean_dec(v_a_1958_);
    crate::leanh::lean_dec_ref(v_a_1957_);
    crate::leanh::lean_dec(v_a_1956_);
    crate::leanh::lean_dec_ref(v_a_1955_);
    return v_res_1960_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalNat___lam__0(
    mut v_e_1961_: *mut crate::leanh::LeanObject,
    mut v___y_1962_: *mut crate::leanh::LeanObject,
    mut v___y_1963_: *mut crate::leanh::LeanObject,
    mut v___y_1964_: *mut crate::leanh::LeanObject,
    mut v___y_1965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1973_: u8 = 0;
    let mut v_val_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1979_: u8 = 0;
    let mut v_a_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1983_: u8 = 0;
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1987_: u8 = 0;
    let mut v_a_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1991_: u8 = 0;
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1995_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_1965_);
                crate::leanh::lean_inc_ref(v___y_1964_);
                crate::leanh::lean_inc(v___y_1963_);
                crate::leanh::lean_inc_ref(v___y_1962_);
                v___x_1967_ = lean_whnf(
                    v_e_1961_,
                    v___y_1962_,
                    v___y_1963_,
                    v___y_1964_,
                    v___y_1965_,
                );
                if crate::leanh::lean_obj_tag(v___x_1967_) == 0 {
                    v_a_1968_ = crate::leanh::lean_ctor_get(v___x_1967_, 0);
                    crate::leanh::lean_inc_n(v_a_1968_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1967_, 1);
                    v___x_1969_ = l_Lean_Meta_evalNat(
                        v_a_1968_,
                        v___y_1962_,
                        v___y_1963_,
                        v___y_1964_,
                        v___y_1965_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1969_) == 0 {
                        v_a_1970_ = crate::leanh::lean_ctor_get(v___x_1969_, 0);
                        v_isSharedCheck_1979_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1969_)) as u8;
                        if v_isSharedCheck_1979_ == 0 {
                            v___x_1972_ = v___x_1969_;
                            v_isShared_1973_ = v_isSharedCheck_1979_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1970_);
                            crate::leanh::lean_dec(v___x_1969_);
                            v___x_1972_ = crate::leanh::lean_box(0);
                            v_isShared_1973_ = v_isSharedCheck_1979_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1968_);
                        v_a_1980_ = crate::leanh::lean_ctor_get(v___x_1969_, 0);
                        v_isSharedCheck_1987_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1969_)) as u8;
                        if v_isSharedCheck_1987_ == 0 {
                            v___x_1982_ = v___x_1969_;
                            v_isShared_1983_ = v_isSharedCheck_1987_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1980_);
                            crate::leanh::lean_dec(v___x_1969_);
                            v___x_1982_ = crate::leanh::lean_box(0);
                            v_isShared_1983_ = v_isSharedCheck_1987_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_1988_ = crate::leanh::lean_ctor_get(v___x_1967_, 0);
                    v_isSharedCheck_1995_ = (!crate::leanh::lean_is_exclusive(v___x_1967_)) as u8;
                    if v_isSharedCheck_1995_ == 0 {
                        v___x_1990_ = v___x_1967_;
                        v_isShared_1991_ = v_isSharedCheck_1995_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1988_);
                        crate::leanh::lean_dec(v___x_1967_);
                        v___x_1990_ = crate::leanh::lean_box(0);
                        v_isShared_1991_ = v_isSharedCheck_1995_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1970_) == 1 {
                    crate::leanh::lean_dec(v_a_1968_);
                    v_val_1974_ = crate::leanh::lean_ctor_get(v_a_1970_, 0);
                    crate::leanh::lean_inc(v_val_1974_);
                    crate::leanh::lean_dec_ref_known(v_a_1970_, 1);
                    if v_isShared_1973_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1972_, 0, v_val_1974_);
                        v___x_1976_ = v___x_1972_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1977_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_val_1974_);
                        v___x_1976_ = v_reuseFailAlloc_1977_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1972_);
                    crate::leanh::lean_dec(v_a_1970_);
                    v___x_1978_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_a_1968_,
                            v___y_1962_,
                            v___y_1963_,
                            v___y_1964_,
                            v___y_1965_,
                        );
                    return v___x_1978_;
                }
            }
            2 => {
                return v___x_1976_;
            }
            3 => {
                if v_isShared_1983_ == 0 {
                    v___x_1985_ = v___x_1982_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1986_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
                    v___x_1985_ = v_reuseFailAlloc_1986_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1985_;
            }
            5 => {
                if v_isShared_1991_ == 0 {
                    v___x_1993_ = v___x_1990_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1994_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
                    v___x_1993_ = v_reuseFailAlloc_1994_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1993_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instReduceEvalNat___lam__0___boxed(
    mut v_e_1996_: *mut crate::leanh::LeanObject,
    mut v___y_1997_: *mut crate::leanh::LeanObject,
    mut v___y_1998_: *mut crate::leanh::LeanObject,
    mut v___y_1999_: *mut crate::leanh::LeanObject,
    mut v___y_2000_: *mut crate::leanh::LeanObject,
    mut v___y_2001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2002_ = l_Lean_Meta_instReduceEvalNat___lam__0(
        v_e_1996_,
        v___y_1997_,
        v___y_1998_,
        v___y_1999_,
        v___y_2000_,
    );
    crate::leanh::lean_dec(v___y_2000_);
    crate::leanh::lean_dec_ref(v___y_1999_);
    crate::leanh::lean_dec(v___y_1998_);
    crate::leanh::lean_dec_ref(v___y_1997_);
    return v_res_2002_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalOption___private__1___redArg(
    mut v_inst_2014_: *mut crate::leanh::LeanObject,
    mut v_e_2015_: *mut crate::leanh::LeanObject,
    mut v_a_2016_: *mut crate::leanh::LeanObject,
    mut v_a_2017_: *mut crate::leanh::LeanObject,
    mut v_a_2018_: *mut crate::leanh::LeanObject,
    mut v_a_2019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2025_: u8 = 0;
    let mut v___y_2027_: u8 = 0;
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2034_: u8 = 0;
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2039_: u8 = 0;
    let mut v_a_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2043_: u8 = 0;
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2047_: u8 = 0;
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2052_: u8 = 0;
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: u8 = 0;
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: u8 = 0;
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: u8 = 0;
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: u8 = 0;
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2066_: u8 = 0;
    let mut v_a_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2070_: u8 = 0;
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2074_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_2019_);
                crate::leanh::lean_inc_ref(v_a_2018_);
                crate::leanh::lean_inc(v_a_2017_);
                crate::leanh::lean_inc_ref(v_a_2016_);
                v___x_2021_ = lean_whnf(v_e_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
                if crate::leanh::lean_obj_tag(v___x_2021_) == 0 {
                    v_a_2022_ = crate::leanh::lean_ctor_get(v___x_2021_, 0);
                    v_isSharedCheck_2066_ = (!crate::leanh::lean_is_exclusive(v___x_2021_)) as u8;
                    if v_isSharedCheck_2066_ == 0 {
                        v___x_2024_ = v___x_2021_;
                        v_isShared_2025_ = v_isSharedCheck_2066_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2022_);
                        crate::leanh::lean_dec(v___x_2021_);
                        v___x_2024_ = crate::leanh::lean_box(0);
                        v_isShared_2025_ = v_isSharedCheck_2066_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_2014_);
                    v_a_2067_ = crate::leanh::lean_ctor_get(v___x_2021_, 0);
                    v_isSharedCheck_2074_ = (!crate::leanh::lean_is_exclusive(v___x_2021_)) as u8;
                    if v_isSharedCheck_2074_ == 0 {
                        v___x_2069_ = v___x_2021_;
                        v_isShared_2070_ = v_isSharedCheck_2074_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2067_);
                        crate::leanh::lean_dec(v___x_2021_);
                        v___x_2069_ = crate::leanh::lean_box(0);
                        v_isShared_2070_ = v_isSharedCheck_2074_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2048_ = l_Lean_Expr_getAppFn(v_a_2022_);
                if crate::leanh::lean_obj_tag(v___x_2048_) == 4 {
                    v_declName_2049_ = crate::leanh::lean_ctor_get(v___x_2048_, 0);
                    crate::leanh::lean_inc(v_declName_2049_);
                    crate::leanh::lean_dec_ref_known(v___x_2048_, 2);
                    v___x_2050_ = l_Lean_Expr_getAppNumArgs(v_a_2022_);
                    v___x_2061_ =
                        l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4;
                    v___x_2062_ = lean_name_eq(v_declName_2049_, v___x_2061_);
                    if v___x_2062_ == 0 {
                        v___y_2052_ = v___x_2062_;
                        state = 7;
                        continue;
                    } else {
                        v___x_2063_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2064_ = lean_nat_dec_eq(v___x_2050_, v___x_2063_);
                        v___y_2052_ = v___x_2064_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2048_);
                    crate::leanh::lean_del_object(v___x_2024_);
                    crate::leanh::lean_dec_ref(v_inst_2014_);
                    v___x_2065_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_a_2022_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_,
                        );
                    return v___x_2065_;
                }
            }
            2 => {
                if v___y_2027_ == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2014_);
                    v___x_2028_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_a_2022_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_,
                        );
                    return v___x_2028_;
                } else {
                    v___x_2029_ = l_Lean_Expr_appArg_x21(v_a_2022_);
                    crate::leanh::lean_dec(v_a_2022_);
                    v___x_2030_ = l_Lean_Meta_reduceEval___redArg(
                        v_inst_2014_,
                        v___x_2029_,
                        v_a_2016_,
                        v_a_2017_,
                        v_a_2018_,
                        v_a_2019_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2030_) == 0 {
                        v_a_2031_ = crate::leanh::lean_ctor_get(v___x_2030_, 0);
                        v_isSharedCheck_2039_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2030_)) as u8;
                        if v_isSharedCheck_2039_ == 0 {
                            v___x_2033_ = v___x_2030_;
                            v_isShared_2034_ = v_isSharedCheck_2039_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2031_);
                            crate::leanh::lean_dec(v___x_2030_);
                            v___x_2033_ = crate::leanh::lean_box(0);
                            v_isShared_2034_ = v_isSharedCheck_2039_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2040_ = crate::leanh::lean_ctor_get(v___x_2030_, 0);
                        v_isSharedCheck_2047_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2030_)) as u8;
                        if v_isSharedCheck_2047_ == 0 {
                            v___x_2042_ = v___x_2030_;
                            v_isShared_2043_ = v_isSharedCheck_2047_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2040_);
                            crate::leanh::lean_dec(v___x_2030_);
                            v___x_2042_ = crate::leanh::lean_box(0);
                            v_isShared_2043_ = v_isSharedCheck_2047_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_2035_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2035_, 0, v_a_2031_);
                if v_isShared_2034_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2033_, 0, v___x_2035_);
                    v___x_2037_ = v___x_2033_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2038_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
                    v___x_2037_ = v_reuseFailAlloc_2038_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2037_;
            }
            5 => {
                if v_isShared_2043_ == 0 {
                    v___x_2045_ = v___x_2042_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2046_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
                    v___x_2045_ = v_reuseFailAlloc_2046_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2045_;
            }
            7 => {
                if v___y_2052_ == 0 {
                    crate::leanh::lean_del_object(v___x_2024_);
                    v___x_2053_ =
                        l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2;
                    v___x_2054_ = lean_name_eq(v_declName_2049_, v___x_2053_);
                    crate::leanh::lean_dec(v_declName_2049_);
                    if v___x_2054_ == 0 {
                        crate::leanh::lean_dec(v___x_2050_);
                        v___y_2027_ = v___x_2054_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2055_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2056_ = lean_nat_dec_eq(v___x_2050_, v___x_2055_);
                        crate::leanh::lean_dec(v___x_2050_);
                        v___y_2027_ = v___x_2056_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2050_);
                    crate::leanh::lean_dec(v_declName_2049_);
                    crate::leanh::lean_dec(v_a_2022_);
                    crate::leanh::lean_dec_ref(v_inst_2014_);
                    v___x_2057_ = crate::leanh::lean_box(0);
                    if v_isShared_2025_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2024_, 0, v___x_2057_);
                        v___x_2059_ = v___x_2024_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2060_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2057_);
                        v___x_2059_ = v_reuseFailAlloc_2060_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                return v___x_2059_;
            }
            9 => {
                if v_isShared_2070_ == 0 {
                    v___x_2072_ = v___x_2069_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2073_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
                    v___x_2072_ = v_reuseFailAlloc_2073_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2072_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instReduceEvalOption___private__1___redArg___boxed(
    mut v_inst_2075_: *mut crate::leanh::LeanObject,
    mut v_e_2076_: *mut crate::leanh::LeanObject,
    mut v_a_2077_: *mut crate::leanh::LeanObject,
    mut v_a_2078_: *mut crate::leanh::LeanObject,
    mut v_a_2079_: *mut crate::leanh::LeanObject,
    mut v_a_2080_: *mut crate::leanh::LeanObject,
    mut v_a_2081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2082_ = l_Lean_Meta_instReduceEvalOption___private__1___redArg(
        v_inst_2075_,
        v_e_2076_,
        v_a_2077_,
        v_a_2078_,
        v_a_2079_,
        v_a_2080_,
    );
    crate::leanh::lean_dec(v_a_2080_);
    crate::leanh::lean_dec_ref(v_a_2079_);
    crate::leanh::lean_dec(v_a_2078_);
    crate::leanh::lean_dec_ref(v_a_2077_);
    return v_res_2082_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalOption___private__1(
    mut v_00_u03b1_2083_: *mut crate::leanh::LeanObject,
    mut v_inst_2084_: *mut crate::leanh::LeanObject,
    mut v_e_2085_: *mut crate::leanh::LeanObject,
    mut v_a_2086_: *mut crate::leanh::LeanObject,
    mut v_a_2087_: *mut crate::leanh::LeanObject,
    mut v_a_2088_: *mut crate::leanh::LeanObject,
    mut v_a_2089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2095_: u8 = 0;
    let mut v___y_2097_: u8 = 0;
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2104_: u8 = 0;
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2109_: u8 = 0;
    let mut v_a_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2113_: u8 = 0;
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2117_: u8 = 0;
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2122_: u8 = 0;
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: u8 = 0;
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: u8 = 0;
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: u8 = 0;
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: u8 = 0;
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2136_: u8 = 0;
    let mut v_a_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2140_: u8 = 0;
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2144_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_2089_);
                crate::leanh::lean_inc_ref(v_a_2088_);
                crate::leanh::lean_inc(v_a_2087_);
                crate::leanh::lean_inc_ref(v_a_2086_);
                v___x_2091_ = lean_whnf(v_e_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
                if crate::leanh::lean_obj_tag(v___x_2091_) == 0 {
                    v_a_2092_ = crate::leanh::lean_ctor_get(v___x_2091_, 0);
                    v_isSharedCheck_2136_ = (!crate::leanh::lean_is_exclusive(v___x_2091_)) as u8;
                    if v_isSharedCheck_2136_ == 0 {
                        v___x_2094_ = v___x_2091_;
                        v_isShared_2095_ = v_isSharedCheck_2136_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2092_);
                        crate::leanh::lean_dec(v___x_2091_);
                        v___x_2094_ = crate::leanh::lean_box(0);
                        v_isShared_2095_ = v_isSharedCheck_2136_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_2084_);
                    v_a_2137_ = crate::leanh::lean_ctor_get(v___x_2091_, 0);
                    v_isSharedCheck_2144_ = (!crate::leanh::lean_is_exclusive(v___x_2091_)) as u8;
                    if v_isSharedCheck_2144_ == 0 {
                        v___x_2139_ = v___x_2091_;
                        v_isShared_2140_ = v_isSharedCheck_2144_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2137_);
                        crate::leanh::lean_dec(v___x_2091_);
                        v___x_2139_ = crate::leanh::lean_box(0);
                        v_isShared_2140_ = v_isSharedCheck_2144_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2118_ = l_Lean_Expr_getAppFn(v_a_2092_);
                if crate::leanh::lean_obj_tag(v___x_2118_) == 4 {
                    v_declName_2119_ = crate::leanh::lean_ctor_get(v___x_2118_, 0);
                    crate::leanh::lean_inc(v_declName_2119_);
                    crate::leanh::lean_dec_ref_known(v___x_2118_, 2);
                    v___x_2120_ = l_Lean_Expr_getAppNumArgs(v_a_2092_);
                    v___x_2131_ =
                        l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4;
                    v___x_2132_ = lean_name_eq(v_declName_2119_, v___x_2131_);
                    if v___x_2132_ == 0 {
                        v___y_2122_ = v___x_2132_;
                        state = 7;
                        continue;
                    } else {
                        v___x_2133_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2134_ = lean_nat_dec_eq(v___x_2120_, v___x_2133_);
                        v___y_2122_ = v___x_2134_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2118_);
                    crate::leanh::lean_del_object(v___x_2094_);
                    crate::leanh::lean_dec_ref(v_inst_2084_);
                    v___x_2135_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_a_2092_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_,
                        );
                    return v___x_2135_;
                }
            }
            2 => {
                if v___y_2097_ == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2084_);
                    v___x_2098_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_a_2092_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_,
                        );
                    return v___x_2098_;
                } else {
                    v___x_2099_ = l_Lean_Expr_appArg_x21(v_a_2092_);
                    crate::leanh::lean_dec(v_a_2092_);
                    v___x_2100_ = l_Lean_Meta_reduceEval___redArg(
                        v_inst_2084_,
                        v___x_2099_,
                        v_a_2086_,
                        v_a_2087_,
                        v_a_2088_,
                        v_a_2089_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2100_) == 0 {
                        v_a_2101_ = crate::leanh::lean_ctor_get(v___x_2100_, 0);
                        v_isSharedCheck_2109_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2100_)) as u8;
                        if v_isSharedCheck_2109_ == 0 {
                            v___x_2103_ = v___x_2100_;
                            v_isShared_2104_ = v_isSharedCheck_2109_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2101_);
                            crate::leanh::lean_dec(v___x_2100_);
                            v___x_2103_ = crate::leanh::lean_box(0);
                            v_isShared_2104_ = v_isSharedCheck_2109_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2110_ = crate::leanh::lean_ctor_get(v___x_2100_, 0);
                        v_isSharedCheck_2117_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2100_)) as u8;
                        if v_isSharedCheck_2117_ == 0 {
                            v___x_2112_ = v___x_2100_;
                            v_isShared_2113_ = v_isSharedCheck_2117_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2110_);
                            crate::leanh::lean_dec(v___x_2100_);
                            v___x_2112_ = crate::leanh::lean_box(0);
                            v_isShared_2113_ = v_isSharedCheck_2117_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_2105_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2105_, 0, v_a_2101_);
                if v_isShared_2104_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2103_, 0, v___x_2105_);
                    v___x_2107_ = v___x_2103_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2108_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
                    v___x_2107_ = v_reuseFailAlloc_2108_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2107_;
            }
            5 => {
                if v_isShared_2113_ == 0 {
                    v___x_2115_ = v___x_2112_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2116_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
                    v___x_2115_ = v_reuseFailAlloc_2116_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2115_;
            }
            7 => {
                if v___y_2122_ == 0 {
                    crate::leanh::lean_del_object(v___x_2094_);
                    v___x_2123_ =
                        l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2;
                    v___x_2124_ = lean_name_eq(v_declName_2119_, v___x_2123_);
                    crate::leanh::lean_dec(v_declName_2119_);
                    if v___x_2124_ == 0 {
                        crate::leanh::lean_dec(v___x_2120_);
                        v___y_2097_ = v___x_2124_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2125_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2126_ = lean_nat_dec_eq(v___x_2120_, v___x_2125_);
                        crate::leanh::lean_dec(v___x_2120_);
                        v___y_2097_ = v___x_2126_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2120_);
                    crate::leanh::lean_dec(v_declName_2119_);
                    crate::leanh::lean_dec(v_a_2092_);
                    crate::leanh::lean_dec_ref(v_inst_2084_);
                    v___x_2127_ = crate::leanh::lean_box(0);
                    if v_isShared_2095_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2094_, 0, v___x_2127_);
                        v___x_2129_ = v___x_2094_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2130_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2127_);
                        v___x_2129_ = v_reuseFailAlloc_2130_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                return v___x_2129_;
            }
            9 => {
                if v_isShared_2140_ == 0 {
                    v___x_2142_ = v___x_2139_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2143_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
                    v___x_2142_ = v_reuseFailAlloc_2143_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2142_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instReduceEvalOption___private__1___boxed(
    mut v_00_u03b1_2145_: *mut crate::leanh::LeanObject,
    mut v_inst_2146_: *mut crate::leanh::LeanObject,
    mut v_e_2147_: *mut crate::leanh::LeanObject,
    mut v_a_2148_: *mut crate::leanh::LeanObject,
    mut v_a_2149_: *mut crate::leanh::LeanObject,
    mut v_a_2150_: *mut crate::leanh::LeanObject,
    mut v_a_2151_: *mut crate::leanh::LeanObject,
    mut v_a_2152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2153_ = l_Lean_Meta_instReduceEvalOption___private__1(
        v_00_u03b1_2145_,
        v_inst_2146_,
        v_e_2147_,
        v_a_2148_,
        v_a_2149_,
        v_a_2150_,
        v_a_2151_,
    );
    crate::leanh::lean_dec(v_a_2151_);
    crate::leanh::lean_dec_ref(v_a_2150_);
    crate::leanh::lean_dec(v_a_2149_);
    crate::leanh::lean_dec_ref(v_a_2148_);
    return v_res_2153_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalOption___redArg___lam__0(
    mut v_inst_2154_: *mut crate::leanh::LeanObject,
    mut v_e_2155_: *mut crate::leanh::LeanObject,
    mut v___y_2156_: *mut crate::leanh::LeanObject,
    mut v___y_2157_: *mut crate::leanh::LeanObject,
    mut v___y_2158_: *mut crate::leanh::LeanObject,
    mut v___y_2159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2165_: u8 = 0;
    let mut v___y_2167_: u8 = 0;
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2174_: u8 = 0;
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2179_: u8 = 0;
    let mut v_a_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2183_: u8 = 0;
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2187_: u8 = 0;
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2192_: u8 = 0;
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: u8 = 0;
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: u8 = 0;
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: u8 = 0;
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: u8 = 0;
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2206_: u8 = 0;
    let mut v_a_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2210_: u8 = 0;
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2214_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_2159_);
                crate::leanh::lean_inc_ref(v___y_2158_);
                crate::leanh::lean_inc(v___y_2157_);
                crate::leanh::lean_inc_ref(v___y_2156_);
                v___x_2161_ = lean_whnf(
                    v_e_2155_,
                    v___y_2156_,
                    v___y_2157_,
                    v___y_2158_,
                    v___y_2159_,
                );
                if crate::leanh::lean_obj_tag(v___x_2161_) == 0 {
                    v_a_2162_ = crate::leanh::lean_ctor_get(v___x_2161_, 0);
                    v_isSharedCheck_2206_ = (!crate::leanh::lean_is_exclusive(v___x_2161_)) as u8;
                    if v_isSharedCheck_2206_ == 0 {
                        v___x_2164_ = v___x_2161_;
                        v_isShared_2165_ = v_isSharedCheck_2206_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2162_);
                        crate::leanh::lean_dec(v___x_2161_);
                        v___x_2164_ = crate::leanh::lean_box(0);
                        v_isShared_2165_ = v_isSharedCheck_2206_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_2154_);
                    v_a_2207_ = crate::leanh::lean_ctor_get(v___x_2161_, 0);
                    v_isSharedCheck_2214_ = (!crate::leanh::lean_is_exclusive(v___x_2161_)) as u8;
                    if v_isSharedCheck_2214_ == 0 {
                        v___x_2209_ = v___x_2161_;
                        v_isShared_2210_ = v_isSharedCheck_2214_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2207_);
                        crate::leanh::lean_dec(v___x_2161_);
                        v___x_2209_ = crate::leanh::lean_box(0);
                        v_isShared_2210_ = v_isSharedCheck_2214_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2188_ = l_Lean_Expr_getAppFn(v_a_2162_);
                if crate::leanh::lean_obj_tag(v___x_2188_) == 4 {
                    v_declName_2189_ = crate::leanh::lean_ctor_get(v___x_2188_, 0);
                    crate::leanh::lean_inc(v_declName_2189_);
                    crate::leanh::lean_dec_ref_known(v___x_2188_, 2);
                    v___x_2190_ = l_Lean_Expr_getAppNumArgs(v_a_2162_);
                    v___x_2201_ =
                        l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4;
                    v___x_2202_ = lean_name_eq(v_declName_2189_, v___x_2201_);
                    if v___x_2202_ == 0 {
                        v___y_2192_ = v___x_2202_;
                        state = 7;
                        continue;
                    } else {
                        v___x_2203_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2204_ = lean_nat_dec_eq(v___x_2190_, v___x_2203_);
                        v___y_2192_ = v___x_2204_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2188_);
                    crate::leanh::lean_del_object(v___x_2164_);
                    crate::leanh::lean_dec_ref(v_inst_2154_);
                    v___x_2205_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_a_2162_,
                            v___y_2156_,
                            v___y_2157_,
                            v___y_2158_,
                            v___y_2159_,
                        );
                    return v___x_2205_;
                }
            }
            2 => {
                if v___y_2167_ == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2154_);
                    v___x_2168_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_a_2162_,
                            v___y_2156_,
                            v___y_2157_,
                            v___y_2158_,
                            v___y_2159_,
                        );
                    return v___x_2168_;
                } else {
                    v___x_2169_ = l_Lean_Expr_appArg_x21(v_a_2162_);
                    crate::leanh::lean_dec(v_a_2162_);
                    v___x_2170_ = l_Lean_Meta_reduceEval___redArg(
                        v_inst_2154_,
                        v___x_2169_,
                        v___y_2156_,
                        v___y_2157_,
                        v___y_2158_,
                        v___y_2159_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2170_) == 0 {
                        v_a_2171_ = crate::leanh::lean_ctor_get(v___x_2170_, 0);
                        v_isSharedCheck_2179_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2170_)) as u8;
                        if v_isSharedCheck_2179_ == 0 {
                            v___x_2173_ = v___x_2170_;
                            v_isShared_2174_ = v_isSharedCheck_2179_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2171_);
                            crate::leanh::lean_dec(v___x_2170_);
                            v___x_2173_ = crate::leanh::lean_box(0);
                            v_isShared_2174_ = v_isSharedCheck_2179_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2180_ = crate::leanh::lean_ctor_get(v___x_2170_, 0);
                        v_isSharedCheck_2187_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2170_)) as u8;
                        if v_isSharedCheck_2187_ == 0 {
                            v___x_2182_ = v___x_2170_;
                            v_isShared_2183_ = v_isSharedCheck_2187_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2180_);
                            crate::leanh::lean_dec(v___x_2170_);
                            v___x_2182_ = crate::leanh::lean_box(0);
                            v_isShared_2183_ = v_isSharedCheck_2187_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_2175_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2175_, 0, v_a_2171_);
                if v_isShared_2174_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2173_, 0, v___x_2175_);
                    v___x_2177_ = v___x_2173_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2178_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2175_);
                    v___x_2177_ = v_reuseFailAlloc_2178_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2177_;
            }
            5 => {
                if v_isShared_2183_ == 0 {
                    v___x_2185_ = v___x_2182_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2186_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
                    v___x_2185_ = v_reuseFailAlloc_2186_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2185_;
            }
            7 => {
                if v___y_2192_ == 0 {
                    crate::leanh::lean_del_object(v___x_2164_);
                    v___x_2193_ =
                        l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2;
                    v___x_2194_ = lean_name_eq(v_declName_2189_, v___x_2193_);
                    crate::leanh::lean_dec(v_declName_2189_);
                    if v___x_2194_ == 0 {
                        crate::leanh::lean_dec(v___x_2190_);
                        v___y_2167_ = v___x_2194_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2195_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2196_ = lean_nat_dec_eq(v___x_2190_, v___x_2195_);
                        crate::leanh::lean_dec(v___x_2190_);
                        v___y_2167_ = v___x_2196_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2190_);
                    crate::leanh::lean_dec(v_declName_2189_);
                    crate::leanh::lean_dec(v_a_2162_);
                    crate::leanh::lean_dec_ref(v_inst_2154_);
                    v___x_2197_ = crate::leanh::lean_box(0);
                    if v_isShared_2165_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2164_, 0, v___x_2197_);
                        v___x_2199_ = v___x_2164_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2200_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
                        v___x_2199_ = v_reuseFailAlloc_2200_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                return v___x_2199_;
            }
            9 => {
                if v_isShared_2210_ == 0 {
                    v___x_2212_ = v___x_2209_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2213_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
                    v___x_2212_ = v_reuseFailAlloc_2213_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2212_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instReduceEvalOption___redArg___lam__0___boxed(
    mut v_inst_2215_: *mut crate::leanh::LeanObject,
    mut v_e_2216_: *mut crate::leanh::LeanObject,
    mut v___y_2217_: *mut crate::leanh::LeanObject,
    mut v___y_2218_: *mut crate::leanh::LeanObject,
    mut v___y_2219_: *mut crate::leanh::LeanObject,
    mut v___y_2220_: *mut crate::leanh::LeanObject,
    mut v___y_2221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2222_ = l_Lean_Meta_instReduceEvalOption___redArg___lam__0(
        v_inst_2215_,
        v_e_2216_,
        v___y_2217_,
        v___y_2218_,
        v___y_2219_,
        v___y_2220_,
    );
    crate::leanh::lean_dec(v___y_2220_);
    crate::leanh::lean_dec_ref(v___y_2219_);
    crate::leanh::lean_dec(v___y_2218_);
    crate::leanh::lean_dec_ref(v___y_2217_);
    return v_res_2222_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalOption___redArg(
    mut v_inst_2223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2224_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_instReduceEvalOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2224_, 0, v_inst_2223_);
    return v___f_2224_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalOption(
    mut v_00_u03b1_2225_: *mut crate::leanh::LeanObject,
    mut v_inst_2226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2227_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_instReduceEvalOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2227_, 0, v_inst_2226_);
    return v___f_2227_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalString___private__1(
    mut v_e_2228_: *mut crate::leanh::LeanObject,
    mut v_a_2229_: *mut crate::leanh::LeanObject,
    mut v_a_2230_: *mut crate::leanh::LeanObject,
    mut v_a_2231_: *mut crate::leanh::LeanObject,
    mut v_a_2232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2238_: u8 = 0;
    let mut v_a_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2246_: u8 = 0;
    let mut v_a_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2250_: u8 = 0;
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2254_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_2232_);
                crate::leanh::lean_inc_ref(v_a_2231_);
                crate::leanh::lean_inc(v_a_2230_);
                crate::leanh::lean_inc_ref(v_a_2229_);
                crate::leanh::lean_inc_ref(v_e_2228_);
                v___x_2234_ = lean_whnf(v_e_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
                if crate::leanh::lean_obj_tag(v___x_2234_) == 0 {
                    v_a_2235_ = crate::leanh::lean_ctor_get(v___x_2234_, 0);
                    v_isSharedCheck_2246_ = (!crate::leanh::lean_is_exclusive(v___x_2234_)) as u8;
                    if v_isSharedCheck_2246_ == 0 {
                        v___x_2237_ = v___x_2234_;
                        v_isShared_2238_ = v_isSharedCheck_2246_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2235_);
                        crate::leanh::lean_dec(v___x_2234_);
                        v___x_2237_ = crate::leanh::lean_box(0);
                        v_isShared_2238_ = v_isSharedCheck_2246_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2228_);
                    v_a_2247_ = crate::leanh::lean_ctor_get(v___x_2234_, 0);
                    v_isSharedCheck_2254_ = (!crate::leanh::lean_is_exclusive(v___x_2234_)) as u8;
                    if v_isSharedCheck_2254_ == 0 {
                        v___x_2249_ = v___x_2234_;
                        v_isShared_2250_ = v_isSharedCheck_2254_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2247_);
                        crate::leanh::lean_dec(v___x_2234_);
                        v___x_2249_ = crate::leanh::lean_box(0);
                        v_isShared_2250_ = v_isSharedCheck_2254_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2235_) == 9 {
                    v_a_2239_ = crate::leanh::lean_ctor_get(v_a_2235_, 0);
                    crate::leanh::lean_inc_ref(v_a_2239_);
                    crate::leanh::lean_dec_ref_known(v_a_2235_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2239_) == 1 {
                        crate::leanh::lean_dec_ref(v_e_2228_);
                        v_val_2240_ = crate::leanh::lean_ctor_get(v_a_2239_, 0);
                        crate::leanh::lean_inc_ref(v_val_2240_);
                        crate::leanh::lean_dec_ref_known(v_a_2239_, 1);
                        if v_isShared_2238_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2237_, 0, v_val_2240_);
                            v___x_2242_ = v___x_2237_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2243_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_val_2240_);
                            v___x_2242_ = v_reuseFailAlloc_2243_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_a_2239_);
                        crate::leanh::lean_del_object(v___x_2237_);
                        v___x_2244_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
                        return v___x_2244_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2237_);
                    crate::leanh::lean_dec(v_a_2235_);
                    v___x_2245_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_e_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_,
                        );
                    return v___x_2245_;
                }
            }
            2 => {
                return v___x_2242_;
            }
            3 => {
                if v_isShared_2250_ == 0 {
                    v___x_2252_ = v___x_2249_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2253_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
                    v___x_2252_ = v_reuseFailAlloc_2253_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2252_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instReduceEvalString___private__1___boxed(
    mut v_e_2255_: *mut crate::leanh::LeanObject,
    mut v_a_2256_: *mut crate::leanh::LeanObject,
    mut v_a_2257_: *mut crate::leanh::LeanObject,
    mut v_a_2258_: *mut crate::leanh::LeanObject,
    mut v_a_2259_: *mut crate::leanh::LeanObject,
    mut v_a_2260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2261_ = l_Lean_Meta_instReduceEvalString___private__1(
        v_e_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_,
    );
    crate::leanh::lean_dec(v_a_2259_);
    crate::leanh::lean_dec_ref(v_a_2258_);
    crate::leanh::lean_dec(v_a_2257_);
    crate::leanh::lean_dec_ref(v_a_2256_);
    return v_res_2261_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalString___lam__0(
    mut v_e_2262_: *mut crate::leanh::LeanObject,
    mut v___y_2263_: *mut crate::leanh::LeanObject,
    mut v___y_2264_: *mut crate::leanh::LeanObject,
    mut v___y_2265_: *mut crate::leanh::LeanObject,
    mut v___y_2266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2272_: u8 = 0;
    let mut v_a_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2280_: u8 = 0;
    let mut v_a_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2284_: u8 = 0;
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_2266_);
                crate::leanh::lean_inc_ref(v___y_2265_);
                crate::leanh::lean_inc(v___y_2264_);
                crate::leanh::lean_inc_ref(v___y_2263_);
                crate::leanh::lean_inc_ref(v_e_2262_);
                v___x_2268_ = lean_whnf(
                    v_e_2262_,
                    v___y_2263_,
                    v___y_2264_,
                    v___y_2265_,
                    v___y_2266_,
                );
                if crate::leanh::lean_obj_tag(v___x_2268_) == 0 {
                    v_a_2269_ = crate::leanh::lean_ctor_get(v___x_2268_, 0);
                    v_isSharedCheck_2280_ = (!crate::leanh::lean_is_exclusive(v___x_2268_)) as u8;
                    if v_isSharedCheck_2280_ == 0 {
                        v___x_2271_ = v___x_2268_;
                        v_isShared_2272_ = v_isSharedCheck_2280_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2269_);
                        crate::leanh::lean_dec(v___x_2268_);
                        v___x_2271_ = crate::leanh::lean_box(0);
                        v_isShared_2272_ = v_isSharedCheck_2280_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2262_);
                    v_a_2281_ = crate::leanh::lean_ctor_get(v___x_2268_, 0);
                    v_isSharedCheck_2288_ = (!crate::leanh::lean_is_exclusive(v___x_2268_)) as u8;
                    if v_isSharedCheck_2288_ == 0 {
                        v___x_2283_ = v___x_2268_;
                        v_isShared_2284_ = v_isSharedCheck_2288_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2281_);
                        crate::leanh::lean_dec(v___x_2268_);
                        v___x_2283_ = crate::leanh::lean_box(0);
                        v_isShared_2284_ = v_isSharedCheck_2288_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2269_) == 9 {
                    v_a_2273_ = crate::leanh::lean_ctor_get(v_a_2269_, 0);
                    crate::leanh::lean_inc_ref(v_a_2273_);
                    crate::leanh::lean_dec_ref_known(v_a_2269_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2273_) == 1 {
                        crate::leanh::lean_dec_ref(v_e_2262_);
                        v_val_2274_ = crate::leanh::lean_ctor_get(v_a_2273_, 0);
                        crate::leanh::lean_inc_ref(v_val_2274_);
                        crate::leanh::lean_dec_ref_known(v_a_2273_, 1);
                        if v_isShared_2272_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2271_, 0, v_val_2274_);
                            v___x_2276_ = v___x_2271_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2277_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_val_2274_);
                            v___x_2276_ = v_reuseFailAlloc_2277_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_a_2273_);
                        crate::leanh::lean_del_object(v___x_2271_);
                        v___x_2278_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
                        return v___x_2278_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2271_);
                    crate::leanh::lean_dec(v_a_2269_);
                    v___x_2279_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_e_2262_,
                            v___y_2263_,
                            v___y_2264_,
                            v___y_2265_,
                            v___y_2266_,
                        );
                    return v___x_2279_;
                }
            }
            2 => {
                return v___x_2276_;
            }
            3 => {
                if v_isShared_2284_ == 0 {
                    v___x_2286_ = v___x_2283_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2287_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
                    v___x_2286_ = v_reuseFailAlloc_2287_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2286_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instReduceEvalString___lam__0___boxed(
    mut v_e_2289_: *mut crate::leanh::LeanObject,
    mut v___y_2290_: *mut crate::leanh::LeanObject,
    mut v___y_2291_: *mut crate::leanh::LeanObject,
    mut v___y_2292_: *mut crate::leanh::LeanObject,
    mut v___y_2293_: *mut crate::leanh::LeanObject,
    mut v___y_2294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2295_ = l_Lean_Meta_instReduceEvalString___lam__0(
        v_e_2289_,
        v___y_2290_,
        v___y_2291_,
        v___y_2292_,
        v___y_2293_,
    );
    crate::leanh::lean_dec(v___y_2293_);
    crate::leanh::lean_dec_ref(v___y_2292_);
    crate::leanh::lean_dec(v___y_2291_);
    crate::leanh::lean_dec_ref(v___y_2290_);
    return v_res_2295_;
}
pub unsafe fn l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(
    mut v_e_2298_: *mut crate::leanh::LeanObject,
    mut v_a_2299_: *mut crate::leanh::LeanObject,
    mut v_a_2300_: *mut crate::leanh::LeanObject,
    mut v_a_2301_: *mut crate::leanh::LeanObject,
    mut v_a_2302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2305_: u8 = 0;
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_2307_: u8 = 0;
    let mut v_ctxApprox_2308_: u8 = 0;
    let mut v_quasiPatternApprox_2309_: u8 = 0;
    let mut v_constApprox_2310_: u8 = 0;
    let mut v_isDefEqStuckEx_2311_: u8 = 0;
    let mut v_unificationHints_2312_: u8 = 0;
    let mut v_proofIrrelevance_2313_: u8 = 0;
    let mut v_assignSyntheticOpaque_2314_: u8 = 0;
    let mut v_offsetCnstrs_2315_: u8 = 0;
    let mut v_etaStruct_2316_: u8 = 0;
    let mut v_univApprox_2317_: u8 = 0;
    let mut v_iota_2318_: u8 = 0;
    let mut v_beta_2319_: u8 = 0;
    let mut v_proj_2320_: u8 = 0;
    let mut v_zeta_2321_: u8 = 0;
    let mut v_zetaDelta_2322_: u8 = 0;
    let mut v_zetaUnused_2323_: u8 = 0;
    let mut v_zetaHave_2324_: u8 = 0;
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2327_: u8 = 0;
    let mut v_trackZetaDelta_2328_: u8 = 0;
    let mut v_zetaDeltaSet_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2335_: u8 = 0;
    let mut v_inTypeClassResolution_2336_: u8 = 0;
    let mut v_cacheInferType_2337_: u8 = 0;
    let mut v_config_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: u64 = 0;
    let mut v___x_2341_: u64 = 0;
    let mut v___x_2342_: u64 = 0;
    let mut v___x_2343_: u64 = 0;
    let mut v___x_2344_: u64 = 0;
    let mut v_key_2345_: u64 = 0;
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2354_: u8 = 0;
    let mut v_val_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2360_: u8 = 0;
    let mut v_a_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2364_: u8 = 0;
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2368_: u8 = 0;
    let mut v_a_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2372_: u8 = 0;
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2376_: u8 = 0;
    let mut v_reuseFailAlloc_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2378_: u8 = 0;
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transparency_2380_: u8 = 0;
    let mut v___x_2381_: u8 = 0;
    let mut v___x_2382_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2379_ = l_Lean_Meta_Context_config(v_a_2299_);
                v_transparency_2380_ = crate::leanh::lean_ctor_get_uint8(v___x_2379_, 9 as u32);
                crate::leanh::lean_dec_ref(v___x_2379_);
                v___x_2381_ = 1;
                v___x_2382_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2380_, v___x_2381_);
                if v___x_2382_ == 0 {
                    v___y_2305_ = v_transparency_2380_;
                    state = 1;
                    continue;
                } else {
                    v___y_2305_ = v___x_2381_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2306_ = l_Lean_Meta_Context_config(v_a_2299_);
                v_foApprox_2307_ = crate::leanh::lean_ctor_get_uint8(v___x_2306_, 0 as u32);
                v_ctxApprox_2308_ = crate::leanh::lean_ctor_get_uint8(v___x_2306_, 1 as u32);
                v_quasiPatternApprox_2309_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_2306_, 2 as u32);
                v_constApprox_2310_ = crate::leanh::lean_ctor_get_uint8(v___x_2306_, 3 as u32);
                v_isDefEqStuckEx_2311_ = crate::leanh::lean_ctor_get_uint8(v___x_2306_, 4 as u32);
                v_unificationHints_2312_ = crate::leanh::lean_ctor_get_uint8(v___x_2306_, 5 as u32);
                v_proofIrrelevance_2313_ = crate::leanh::lean_ctor_get_uint8(v___x_2306_, 6 as u32);
                v_assignSyntheticOpaque_2314_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_2306_, 7 as u32);
                v_offsetCnstrs_2315_ = crate::leanh::lean_ctor_get_uint8(v___x_2306_, 8 as u32);
                v_etaStruct_2316_ = crate::leanh::lean_ctor_get_uint8(v___x_2306_, 10 as u32);
                v_univApprox_2317_ = crate::leanh::lean_ctor_get_uint8(v___x_2306_, 11 as u32);
                v_iota_2318_ = crate::leanh::lean_ctor_get_uint8(v___x_2306_, 12 as u32);
                v_beta_2319_ = crate::leanh::lean_ctor_get_uint8(v___x_2306_, 13 as u32);
                v_proj_2320_ = crate::leanh::lean_ctor_get_uint8(v___x_2306_, 14 as u32);
                v_zeta_2321_ = crate::leanh::lean_ctor_get_uint8(v___x_2306_, 15 as u32);
                v_zetaDelta_2322_ = crate::leanh::lean_ctor_get_uint8(v___x_2306_, 16 as u32);
                v_zetaUnused_2323_ = crate::leanh::lean_ctor_get_uint8(v___x_2306_, 17 as u32);
                v_zetaHave_2324_ = crate::leanh::lean_ctor_get_uint8(v___x_2306_, 18 as u32);
                v_isSharedCheck_2378_ = (!crate::leanh::lean_is_exclusive(v___x_2306_)) as u8;
                if v_isSharedCheck_2378_ == 0 {
                    v___x_2326_ = v___x_2306_;
                    v_isShared_2327_ = v_isSharedCheck_2378_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2306_);
                    v___x_2326_ = crate::leanh::lean_box(0);
                    v_isShared_2327_ = v_isSharedCheck_2378_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_trackZetaDelta_2328_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2299_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2329_ = crate::leanh::lean_ctor_get(v_a_2299_, 1);
                v_lctx_2330_ = crate::leanh::lean_ctor_get(v_a_2299_, 2);
                v_localInstances_2331_ = crate::leanh::lean_ctor_get(v_a_2299_, 3);
                v_defEqCtx_x3f_2332_ = crate::leanh::lean_ctor_get(v_a_2299_, 4);
                v_synthPendingDepth_2333_ = crate::leanh::lean_ctor_get(v_a_2299_, 5);
                v_canUnfold_x3f_2334_ = crate::leanh::lean_ctor_get(v_a_2299_, 6);
                v_univApprox_2335_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2299_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2336_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2299_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2337_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2299_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_2327_ == 0 {
                    v_config_2339_ = v___x_2326_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2377_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        0 as u32,
                        v_foApprox_2307_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        1 as u32,
                        v_ctxApprox_2308_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        2 as u32,
                        v_quasiPatternApprox_2309_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        3 as u32,
                        v_constApprox_2310_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        4 as u32,
                        v_isDefEqStuckEx_2311_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        5 as u32,
                        v_unificationHints_2312_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        6 as u32,
                        v_proofIrrelevance_2313_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        7 as u32,
                        v_assignSyntheticOpaque_2314_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        8 as u32,
                        v_offsetCnstrs_2315_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        10 as u32,
                        v_etaStruct_2316_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        11 as u32,
                        v_univApprox_2317_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        12 as u32,
                        v_iota_2318_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        13 as u32,
                        v_beta_2319_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        14 as u32,
                        v_proj_2320_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        15 as u32,
                        v_zeta_2321_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        16 as u32,
                        v_zetaDelta_2322_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        17 as u32,
                        v_zetaUnused_2323_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        18 as u32,
                        v_zetaHave_2324_,
                    );
                    v_config_2339_ = v_reuseFailAlloc_2377_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(v_config_2339_, 9 as u32, v___y_2305_);
                v___x_2340_ = l_Lean_Meta_Context_configKey(v_a_2299_);
                v___x_2341_ = 3u64;
                v___x_2342_ = lean_uint64_shift_right(v___x_2340_, v___x_2341_);
                v___x_2343_ = lean_uint64_shift_left(v___x_2342_, v___x_2341_);
                v___x_2344_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2305_);
                v_key_2345_ = lean_uint64_lor(v___x_2343_, v___x_2344_);
                v___x_2346_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_2346_, 0, v_config_2339_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_2346_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_2345_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_2334_);
                crate::leanh::lean_inc(v_synthPendingDepth_2333_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_2332_);
                crate::leanh::lean_inc_ref(v_localInstances_2331_);
                crate::leanh::lean_inc_ref(v_lctx_2330_);
                crate::leanh::lean_inc(v_zetaDeltaSet_2329_);
                v___x_2347_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_2347_, 0, v___x_2346_);
                crate::leanh::lean_ctor_set(v___x_2347_, 1, v_zetaDeltaSet_2329_);
                crate::leanh::lean_ctor_set(v___x_2347_, 2, v_lctx_2330_);
                crate::leanh::lean_ctor_set(v___x_2347_, 3, v_localInstances_2331_);
                crate::leanh::lean_ctor_set(v___x_2347_, 4, v_defEqCtx_x3f_2332_);
                crate::leanh::lean_ctor_set(v___x_2347_, 5, v_synthPendingDepth_2333_);
                crate::leanh::lean_ctor_set(v___x_2347_, 6, v_canUnfold_x3f_2334_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2347_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2328_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2347_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2335_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2347_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2336_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2347_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2337_,
                );
                crate::leanh::lean_inc(v_a_2302_);
                crate::leanh::lean_inc_ref(v_a_2301_);
                crate::leanh::lean_inc(v_a_2300_);
                crate::leanh::lean_inc_ref(v___x_2347_);
                v___x_2348_ = lean_whnf(v_e_2298_, v___x_2347_, v_a_2300_, v_a_2301_, v_a_2302_);
                if crate::leanh::lean_obj_tag(v___x_2348_) == 0 {
                    v_a_2349_ = crate::leanh::lean_ctor_get(v___x_2348_, 0);
                    crate::leanh::lean_inc_n(v_a_2349_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2348_, 1);
                    v___x_2350_ = l_Lean_Meta_evalNat(
                        v_a_2349_,
                        v___x_2347_,
                        v_a_2300_,
                        v_a_2301_,
                        v_a_2302_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2350_) == 0 {
                        v_a_2351_ = crate::leanh::lean_ctor_get(v___x_2350_, 0);
                        v_isSharedCheck_2360_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2350_)) as u8;
                        if v_isSharedCheck_2360_ == 0 {
                            v___x_2353_ = v___x_2350_;
                            v_isShared_2354_ = v_isSharedCheck_2360_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2351_);
                            crate::leanh::lean_dec(v___x_2350_);
                            v___x_2353_ = crate::leanh::lean_box(0);
                            v_isShared_2354_ = v_isSharedCheck_2360_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2349_);
                        crate::leanh::lean_dec_ref_known(v___x_2347_, 7);
                        v_a_2361_ = crate::leanh::lean_ctor_get(v___x_2350_, 0);
                        v_isSharedCheck_2368_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2350_)) as u8;
                        if v_isSharedCheck_2368_ == 0 {
                            v___x_2363_ = v___x_2350_;
                            v_isShared_2364_ = v_isSharedCheck_2368_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2361_);
                            crate::leanh::lean_dec(v___x_2350_);
                            v___x_2363_ = crate::leanh::lean_box(0);
                            v_isShared_2364_ = v_isSharedCheck_2368_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2347_, 7);
                    v_a_2369_ = crate::leanh::lean_ctor_get(v___x_2348_, 0);
                    v_isSharedCheck_2376_ = (!crate::leanh::lean_is_exclusive(v___x_2348_)) as u8;
                    if v_isSharedCheck_2376_ == 0 {
                        v___x_2371_ = v___x_2348_;
                        v_isShared_2372_ = v_isSharedCheck_2376_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2369_);
                        crate::leanh::lean_dec(v___x_2348_);
                        v___x_2371_ = crate::leanh::lean_box(0);
                        v_isShared_2372_ = v_isSharedCheck_2376_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_2351_) == 1 {
                    crate::leanh::lean_dec(v_a_2349_);
                    crate::leanh::lean_dec_ref_known(v___x_2347_, 7);
                    v_val_2355_ = crate::leanh::lean_ctor_get(v_a_2351_, 0);
                    crate::leanh::lean_inc(v_val_2355_);
                    crate::leanh::lean_dec_ref_known(v_a_2351_, 1);
                    if v_isShared_2354_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2353_, 0, v_val_2355_);
                        v___x_2357_ = v___x_2353_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2358_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_val_2355_);
                        v___x_2357_ = v_reuseFailAlloc_2358_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2353_);
                    crate::leanh::lean_dec(v_a_2351_);
                    v___x_2359_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_a_2349_,
                            v___x_2347_,
                            v_a_2300_,
                            v_a_2301_,
                            v_a_2302_,
                        );
                    crate::leanh::lean_dec_ref_known(v___x_2347_, 7);
                    return v___x_2359_;
                }
            }
            5 => {
                return v___x_2357_;
            }
            6 => {
                if v_isShared_2364_ == 0 {
                    v___x_2366_ = v___x_2363_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2367_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
                    v___x_2366_ = v_reuseFailAlloc_2367_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2366_;
            }
            8 => {
                if v_isShared_2372_ == 0 {
                    v___x_2374_ = v___x_2371_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2375_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
                    v___x_2374_ = v_reuseFailAlloc_2375_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2374_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0___boxed(
    mut v_e_2383_: *mut crate::leanh::LeanObject,
    mut v_a_2384_: *mut crate::leanh::LeanObject,
    mut v_a_2385_: *mut crate::leanh::LeanObject,
    mut v_a_2386_: *mut crate::leanh::LeanObject,
    mut v_a_2387_: *mut crate::leanh::LeanObject,
    mut v_a_2388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2389_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(v_e_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
    crate::leanh::lean_dec(v_a_2387_);
    crate::leanh::lean_dec_ref(v_a_2386_);
    crate::leanh::lean_dec(v_a_2385_);
    crate::leanh::lean_dec_ref(v_a_2384_);
    return v_res_2389_;
}
pub unsafe fn l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(
    mut v_e_2390_: *mut crate::leanh::LeanObject,
    mut v_a_2391_: *mut crate::leanh::LeanObject,
    mut v_a_2392_: *mut crate::leanh::LeanObject,
    mut v_a_2393_: *mut crate::leanh::LeanObject,
    mut v_a_2394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2397_: u8 = 0;
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_2399_: u8 = 0;
    let mut v_ctxApprox_2400_: u8 = 0;
    let mut v_quasiPatternApprox_2401_: u8 = 0;
    let mut v_constApprox_2402_: u8 = 0;
    let mut v_isDefEqStuckEx_2403_: u8 = 0;
    let mut v_unificationHints_2404_: u8 = 0;
    let mut v_proofIrrelevance_2405_: u8 = 0;
    let mut v_assignSyntheticOpaque_2406_: u8 = 0;
    let mut v_offsetCnstrs_2407_: u8 = 0;
    let mut v_etaStruct_2408_: u8 = 0;
    let mut v_univApprox_2409_: u8 = 0;
    let mut v_iota_2410_: u8 = 0;
    let mut v_beta_2411_: u8 = 0;
    let mut v_proj_2412_: u8 = 0;
    let mut v_zeta_2413_: u8 = 0;
    let mut v_zetaDelta_2414_: u8 = 0;
    let mut v_zetaUnused_2415_: u8 = 0;
    let mut v_zetaHave_2416_: u8 = 0;
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2419_: u8 = 0;
    let mut v_trackZetaDelta_2420_: u8 = 0;
    let mut v_zetaDeltaSet_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2427_: u8 = 0;
    let mut v_inTypeClassResolution_2428_: u8 = 0;
    let mut v_cacheInferType_2429_: u8 = 0;
    let mut v_config_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: u64 = 0;
    let mut v___x_2433_: u64 = 0;
    let mut v___x_2434_: u64 = 0;
    let mut v___x_2435_: u64 = 0;
    let mut v___x_2436_: u64 = 0;
    let mut v_key_2437_: u64 = 0;
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2444_: u8 = 0;
    let mut v_a_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2452_: u8 = 0;
    let mut v_a_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2456_: u8 = 0;
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2460_: u8 = 0;
    let mut v_reuseFailAlloc_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2462_: u8 = 0;
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transparency_2464_: u8 = 0;
    let mut v___x_2465_: u8 = 0;
    let mut v___x_2466_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2463_ = l_Lean_Meta_Context_config(v_a_2391_);
                v_transparency_2464_ = crate::leanh::lean_ctor_get_uint8(v___x_2463_, 9 as u32);
                crate::leanh::lean_dec_ref(v___x_2463_);
                v___x_2465_ = 1;
                v___x_2466_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2464_, v___x_2465_);
                if v___x_2466_ == 0 {
                    v___y_2397_ = v_transparency_2464_;
                    state = 1;
                    continue;
                } else {
                    v___y_2397_ = v___x_2465_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2398_ = l_Lean_Meta_Context_config(v_a_2391_);
                v_foApprox_2399_ = crate::leanh::lean_ctor_get_uint8(v___x_2398_, 0 as u32);
                v_ctxApprox_2400_ = crate::leanh::lean_ctor_get_uint8(v___x_2398_, 1 as u32);
                v_quasiPatternApprox_2401_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_2398_, 2 as u32);
                v_constApprox_2402_ = crate::leanh::lean_ctor_get_uint8(v___x_2398_, 3 as u32);
                v_isDefEqStuckEx_2403_ = crate::leanh::lean_ctor_get_uint8(v___x_2398_, 4 as u32);
                v_unificationHints_2404_ = crate::leanh::lean_ctor_get_uint8(v___x_2398_, 5 as u32);
                v_proofIrrelevance_2405_ = crate::leanh::lean_ctor_get_uint8(v___x_2398_, 6 as u32);
                v_assignSyntheticOpaque_2406_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_2398_, 7 as u32);
                v_offsetCnstrs_2407_ = crate::leanh::lean_ctor_get_uint8(v___x_2398_, 8 as u32);
                v_etaStruct_2408_ = crate::leanh::lean_ctor_get_uint8(v___x_2398_, 10 as u32);
                v_univApprox_2409_ = crate::leanh::lean_ctor_get_uint8(v___x_2398_, 11 as u32);
                v_iota_2410_ = crate::leanh::lean_ctor_get_uint8(v___x_2398_, 12 as u32);
                v_beta_2411_ = crate::leanh::lean_ctor_get_uint8(v___x_2398_, 13 as u32);
                v_proj_2412_ = crate::leanh::lean_ctor_get_uint8(v___x_2398_, 14 as u32);
                v_zeta_2413_ = crate::leanh::lean_ctor_get_uint8(v___x_2398_, 15 as u32);
                v_zetaDelta_2414_ = crate::leanh::lean_ctor_get_uint8(v___x_2398_, 16 as u32);
                v_zetaUnused_2415_ = crate::leanh::lean_ctor_get_uint8(v___x_2398_, 17 as u32);
                v_zetaHave_2416_ = crate::leanh::lean_ctor_get_uint8(v___x_2398_, 18 as u32);
                v_isSharedCheck_2462_ = (!crate::leanh::lean_is_exclusive(v___x_2398_)) as u8;
                if v_isSharedCheck_2462_ == 0 {
                    v___x_2418_ = v___x_2398_;
                    v_isShared_2419_ = v_isSharedCheck_2462_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2398_);
                    v___x_2418_ = crate::leanh::lean_box(0);
                    v_isShared_2419_ = v_isSharedCheck_2462_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_trackZetaDelta_2420_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2391_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2421_ = crate::leanh::lean_ctor_get(v_a_2391_, 1);
                v_lctx_2422_ = crate::leanh::lean_ctor_get(v_a_2391_, 2);
                v_localInstances_2423_ = crate::leanh::lean_ctor_get(v_a_2391_, 3);
                v_defEqCtx_x3f_2424_ = crate::leanh::lean_ctor_get(v_a_2391_, 4);
                v_synthPendingDepth_2425_ = crate::leanh::lean_ctor_get(v_a_2391_, 5);
                v_canUnfold_x3f_2426_ = crate::leanh::lean_ctor_get(v_a_2391_, 6);
                v_univApprox_2427_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2391_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2428_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2391_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2429_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2391_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_2419_ == 0 {
                    v_config_2431_ = v___x_2418_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2461_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2461_,
                        0 as u32,
                        v_foApprox_2399_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2461_,
                        1 as u32,
                        v_ctxApprox_2400_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2461_,
                        2 as u32,
                        v_quasiPatternApprox_2401_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2461_,
                        3 as u32,
                        v_constApprox_2402_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2461_,
                        4 as u32,
                        v_isDefEqStuckEx_2403_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2461_,
                        5 as u32,
                        v_unificationHints_2404_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2461_,
                        6 as u32,
                        v_proofIrrelevance_2405_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2461_,
                        7 as u32,
                        v_assignSyntheticOpaque_2406_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2461_,
                        8 as u32,
                        v_offsetCnstrs_2407_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2461_,
                        10 as u32,
                        v_etaStruct_2408_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2461_,
                        11 as u32,
                        v_univApprox_2409_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2461_,
                        12 as u32,
                        v_iota_2410_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2461_,
                        13 as u32,
                        v_beta_2411_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2461_,
                        14 as u32,
                        v_proj_2412_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2461_,
                        15 as u32,
                        v_zeta_2413_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2461_,
                        16 as u32,
                        v_zetaDelta_2414_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2461_,
                        17 as u32,
                        v_zetaUnused_2415_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2461_,
                        18 as u32,
                        v_zetaHave_2416_,
                    );
                    v_config_2431_ = v_reuseFailAlloc_2461_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(v_config_2431_, 9 as u32, v___y_2397_);
                v___x_2432_ = l_Lean_Meta_Context_configKey(v_a_2391_);
                v___x_2433_ = 3u64;
                v___x_2434_ = lean_uint64_shift_right(v___x_2432_, v___x_2433_);
                v___x_2435_ = lean_uint64_shift_left(v___x_2434_, v___x_2433_);
                v___x_2436_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2397_);
                v_key_2437_ = lean_uint64_lor(v___x_2435_, v___x_2436_);
                v___x_2438_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_2438_, 0, v_config_2431_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_2438_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_2437_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_2426_);
                crate::leanh::lean_inc(v_synthPendingDepth_2425_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_2424_);
                crate::leanh::lean_inc_ref(v_localInstances_2423_);
                crate::leanh::lean_inc_ref(v_lctx_2422_);
                crate::leanh::lean_inc(v_zetaDeltaSet_2421_);
                v___x_2439_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_2439_, 0, v___x_2438_);
                crate::leanh::lean_ctor_set(v___x_2439_, 1, v_zetaDeltaSet_2421_);
                crate::leanh::lean_ctor_set(v___x_2439_, 2, v_lctx_2422_);
                crate::leanh::lean_ctor_set(v___x_2439_, 3, v_localInstances_2423_);
                crate::leanh::lean_ctor_set(v___x_2439_, 4, v_defEqCtx_x3f_2424_);
                crate::leanh::lean_ctor_set(v___x_2439_, 5, v_synthPendingDepth_2425_);
                crate::leanh::lean_ctor_set(v___x_2439_, 6, v_canUnfold_x3f_2426_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2439_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2420_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2439_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2427_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2439_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2428_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2439_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2429_,
                );
                crate::leanh::lean_inc(v_a_2394_);
                crate::leanh::lean_inc_ref(v_a_2393_);
                crate::leanh::lean_inc(v_a_2392_);
                crate::leanh::lean_inc_ref(v___x_2439_);
                crate::leanh::lean_inc_ref(v_e_2390_);
                v___x_2440_ = lean_whnf(v_e_2390_, v___x_2439_, v_a_2392_, v_a_2393_, v_a_2394_);
                if crate::leanh::lean_obj_tag(v___x_2440_) == 0 {
                    v_a_2441_ = crate::leanh::lean_ctor_get(v___x_2440_, 0);
                    v_isSharedCheck_2452_ = (!crate::leanh::lean_is_exclusive(v___x_2440_)) as u8;
                    if v_isSharedCheck_2452_ == 0 {
                        v___x_2443_ = v___x_2440_;
                        v_isShared_2444_ = v_isSharedCheck_2452_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2441_);
                        crate::leanh::lean_dec(v___x_2440_);
                        v___x_2443_ = crate::leanh::lean_box(0);
                        v_isShared_2444_ = v_isSharedCheck_2452_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2439_, 7);
                    crate::leanh::lean_dec_ref(v_e_2390_);
                    v_a_2453_ = crate::leanh::lean_ctor_get(v___x_2440_, 0);
                    v_isSharedCheck_2460_ = (!crate::leanh::lean_is_exclusive(v___x_2440_)) as u8;
                    if v_isSharedCheck_2460_ == 0 {
                        v___x_2455_ = v___x_2440_;
                        v_isShared_2456_ = v_isSharedCheck_2460_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2453_);
                        crate::leanh::lean_dec(v___x_2440_);
                        v___x_2455_ = crate::leanh::lean_box(0);
                        v_isShared_2456_ = v_isSharedCheck_2460_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_2441_) == 9 {
                    v_a_2445_ = crate::leanh::lean_ctor_get(v_a_2441_, 0);
                    crate::leanh::lean_inc_ref(v_a_2445_);
                    crate::leanh::lean_dec_ref_known(v_a_2441_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2445_) == 1 {
                        crate::leanh::lean_dec_ref_known(v___x_2439_, 7);
                        crate::leanh::lean_dec_ref(v_e_2390_);
                        v_val_2446_ = crate::leanh::lean_ctor_get(v_a_2445_, 0);
                        crate::leanh::lean_inc_ref(v_val_2446_);
                        crate::leanh::lean_dec_ref_known(v_a_2445_, 1);
                        if v_isShared_2444_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2443_, 0, v_val_2446_);
                            v___x_2448_ = v___x_2443_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_2449_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_val_2446_);
                            v___x_2448_ = v_reuseFailAlloc_2449_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_a_2445_);
                        crate::leanh::lean_del_object(v___x_2443_);
                        v___x_2450_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_2390_, v___x_2439_, v_a_2392_, v_a_2393_, v_a_2394_);
                        crate::leanh::lean_dec_ref_known(v___x_2439_, 7);
                        return v___x_2450_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2443_);
                    crate::leanh::lean_dec(v_a_2441_);
                    v___x_2451_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_e_2390_,
                            v___x_2439_,
                            v_a_2392_,
                            v_a_2393_,
                            v_a_2394_,
                        );
                    crate::leanh::lean_dec_ref_known(v___x_2439_, 7);
                    return v___x_2451_;
                }
            }
            5 => {
                return v___x_2448_;
            }
            6 => {
                if v_isShared_2456_ == 0 {
                    v___x_2458_ = v___x_2455_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2459_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
                    v___x_2458_ = v_reuseFailAlloc_2459_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2458_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1___boxed(
    mut v_e_2467_: *mut crate::leanh::LeanObject,
    mut v_a_2468_: *mut crate::leanh::LeanObject,
    mut v_a_2469_: *mut crate::leanh::LeanObject,
    mut v_a_2470_: *mut crate::leanh::LeanObject,
    mut v_a_2471_: *mut crate::leanh::LeanObject,
    mut v_a_2472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2473_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(v_e_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_);
    crate::leanh::lean_dec(v_a_2471_);
    crate::leanh::lean_dec_ref(v_a_2470_);
    crate::leanh::lean_dec(v_a_2469_);
    crate::leanh::lean_dec_ref(v_a_2468_);
    return v_res_2473_;
}
pub unsafe fn l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(
    mut v___x_2474_: *mut crate::leanh::LeanObject,
    mut v_00___2475_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: u8 = 0;
    v___x_2476_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2477_ = lean_nat_dec_eq(v___x_2474_, v___x_2476_);
    return v___x_2477_;
}
pub unsafe fn l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0___boxed(
    mut v___x_2478_: *mut crate::leanh::LeanObject,
    mut v_00___2479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2480_: u8 = 0;
    let mut v_r_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2480_ =
        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(v___x_2478_, v_00___2479_);
    crate::leanh::lean_dec(v___x_2478_);
    v_r_2481_ = crate::leanh::lean_box((v_res_2480_) as usize);
    return v_r_2481_;
}
pub unsafe fn l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(
    mut v_e_2499_: *mut crate::leanh::LeanObject,
    mut v_a_2500_: *mut crate::leanh::LeanObject,
    mut v_a_2501_: *mut crate::leanh::LeanObject,
    mut v_a_2502_: *mut crate::leanh::LeanObject,
    mut v_a_2503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2509_: u8 = 0;
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2514_: u8 = 0;
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2527_: u8 = 0;
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2532_: u8 = 0;
    let mut v_a_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2536_: u8 = 0;
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2540_: u8 = 0;
    let mut v___y_2542_: u8 = 0;
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: u8 = 0;
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: u8 = 0;
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2558_: u8 = 0;
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2563_: u8 = 0;
    let mut v_a_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2567_: u8 = 0;
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2571_: u8 = 0;
    let mut v___y_2573_: u8 = 0;
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: u8 = 0;
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: u8 = 0;
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: u8 = 0;
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: u8 = 0;
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2587_: u8 = 0;
    let mut v_a_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2591_: u8 = 0;
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2595_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_2503_);
                crate::leanh::lean_inc_ref(v_a_2502_);
                crate::leanh::lean_inc(v_a_2501_);
                crate::leanh::lean_inc_ref(v_a_2500_);
                v___x_2505_ = lean_whnf(v_e_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
                if crate::leanh::lean_obj_tag(v___x_2505_) == 0 {
                    v_a_2506_ = crate::leanh::lean_ctor_get(v___x_2505_, 0);
                    v_isSharedCheck_2587_ = (!crate::leanh::lean_is_exclusive(v___x_2505_)) as u8;
                    if v_isSharedCheck_2587_ == 0 {
                        v___x_2508_ = v___x_2505_;
                        v_isShared_2509_ = v_isSharedCheck_2587_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2506_);
                        crate::leanh::lean_dec(v___x_2505_);
                        v___x_2508_ = crate::leanh::lean_box(0);
                        v_isShared_2509_ = v_isSharedCheck_2587_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2588_ = crate::leanh::lean_ctor_get(v___x_2505_, 0);
                    v_isSharedCheck_2595_ = (!crate::leanh::lean_is_exclusive(v___x_2505_)) as u8;
                    if v_isSharedCheck_2595_ == 0 {
                        v___x_2590_ = v___x_2505_;
                        v_isShared_2591_ = v_isSharedCheck_2595_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2588_);
                        crate::leanh::lean_dec(v___x_2505_);
                        v___x_2590_ = crate::leanh::lean_box(0);
                        v_isShared_2591_ = v_isSharedCheck_2595_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2510_ = l_Lean_Expr_getAppFn(v_a_2506_);
                if crate::leanh::lean_obj_tag(v___x_2510_) == 4 {
                    v_declName_2511_ = crate::leanh::lean_ctor_get(v___x_2510_, 0);
                    crate::leanh::lean_inc(v_declName_2511_);
                    crate::leanh::lean_dec_ref_known(v___x_2510_, 2);
                    v___x_2512_ = l_Lean_Expr_getAppNumArgs(v_a_2506_);
                    v___x_2582_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7;
                    v___x_2583_ = lean_name_eq(v_declName_2511_, v___x_2582_);
                    if v___x_2583_ == 0 {
                        v___y_2573_ = v___x_2583_;
                        state = 12;
                        continue;
                    } else {
                        v___x_2584_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2585_ = lean_nat_dec_eq(v___x_2512_, v___x_2584_);
                        v___y_2573_ = v___x_2585_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2510_);
                    crate::leanh::lean_del_object(v___x_2508_);
                    v___x_2586_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_a_2506_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_,
                        );
                    return v___x_2586_;
                }
            }
            2 => {
                if v___y_2514_ == 0 {
                    crate::leanh::lean_dec(v___x_2512_);
                    v___x_2515_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_a_2506_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_,
                        );
                    return v___x_2515_;
                } else {
                    v___x_2516_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2517_ = lean_nat_sub(v___x_2512_, v___x_2516_);
                    crate::leanh::lean_dec(v___x_2512_);
                    crate::leanh::lean_inc(v___x_2517_);
                    v___x_2518_ = l_Lean_Expr_getRevArg_x21(v_a_2506_, v___x_2517_);
                    v___x_2519_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(
                        v___x_2518_,
                        v_a_2500_,
                        v_a_2501_,
                        v_a_2502_,
                        v_a_2503_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2519_) == 0 {
                        v_a_2520_ = crate::leanh::lean_ctor_get(v___x_2519_, 0);
                        crate::leanh::lean_inc(v_a_2520_);
                        crate::leanh::lean_dec_ref_known(v___x_2519_, 1);
                        v___x_2521_ = lean_nat_sub(v___x_2517_, v___x_2516_);
                        crate::leanh::lean_dec(v___x_2517_);
                        v___x_2522_ = l_Lean_Expr_getRevArg_x21(v_a_2506_, v___x_2521_);
                        crate::leanh::lean_dec(v_a_2506_);
                        v___x_2523_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(v___x_2522_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
                        if crate::leanh::lean_obj_tag(v___x_2523_) == 0 {
                            v_a_2524_ = crate::leanh::lean_ctor_get(v___x_2523_, 0);
                            v_isSharedCheck_2532_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2523_)) as u8;
                            if v_isSharedCheck_2532_ == 0 {
                                v___x_2526_ = v___x_2523_;
                                v_isShared_2527_ = v_isSharedCheck_2532_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2524_);
                                crate::leanh::lean_dec(v___x_2523_);
                                v___x_2526_ = crate::leanh::lean_box(0);
                                v_isShared_2527_ = v_isSharedCheck_2532_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2520_);
                            v_a_2533_ = crate::leanh::lean_ctor_get(v___x_2523_, 0);
                            v_isSharedCheck_2540_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2523_)) as u8;
                            if v_isSharedCheck_2540_ == 0 {
                                v___x_2535_ = v___x_2523_;
                                v_isShared_2536_ = v_isSharedCheck_2540_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2533_);
                                crate::leanh::lean_dec(v___x_2523_);
                                v___x_2535_ = crate::leanh::lean_box(0);
                                v_isShared_2536_ = v_isSharedCheck_2540_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2517_);
                        crate::leanh::lean_dec(v_a_2506_);
                        return v___x_2519_;
                    }
                }
            }
            3 => {
                v___x_2528_ = l_Lean_Name_num___override(v_a_2520_, v_a_2524_);
                if v_isShared_2527_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2526_, 0, v___x_2528_);
                    v___x_2530_ = v___x_2526_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2531_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
                    v___x_2530_ = v_reuseFailAlloc_2531_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2530_;
            }
            5 => {
                if v_isShared_2536_ == 0 {
                    v___x_2538_ = v___x_2535_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2539_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
                    v___x_2538_ = v_reuseFailAlloc_2539_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2538_;
            }
            7 => {
                if v___y_2542_ == 0 {
                    v___x_2543_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3;
                    v___x_2544_ = lean_name_eq(v_declName_2511_, v___x_2543_);
                    crate::leanh::lean_dec(v_declName_2511_);
                    if v___x_2544_ == 0 {
                        v___y_2514_ = v___x_2544_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2545_ = crate::leanh::lean_box(0);
                        v___x_2546_ =
                            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(
                                v___x_2512_,
                                v___x_2545_,
                            );
                        v___y_2514_ = v___x_2546_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_2511_);
                    v___x_2547_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2548_ = lean_nat_sub(v___x_2512_, v___x_2547_);
                    crate::leanh::lean_dec(v___x_2512_);
                    crate::leanh::lean_inc(v___x_2548_);
                    v___x_2549_ = l_Lean_Expr_getRevArg_x21(v_a_2506_, v___x_2548_);
                    v___x_2550_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(
                        v___x_2549_,
                        v_a_2500_,
                        v_a_2501_,
                        v_a_2502_,
                        v_a_2503_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2550_) == 0 {
                        v_a_2551_ = crate::leanh::lean_ctor_get(v___x_2550_, 0);
                        crate::leanh::lean_inc(v_a_2551_);
                        crate::leanh::lean_dec_ref_known(v___x_2550_, 1);
                        v___x_2552_ = lean_nat_sub(v___x_2548_, v___x_2547_);
                        crate::leanh::lean_dec(v___x_2548_);
                        v___x_2553_ = l_Lean_Expr_getRevArg_x21(v_a_2506_, v___x_2552_);
                        crate::leanh::lean_dec(v_a_2506_);
                        v___x_2554_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(v___x_2553_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
                        if crate::leanh::lean_obj_tag(v___x_2554_) == 0 {
                            v_a_2555_ = crate::leanh::lean_ctor_get(v___x_2554_, 0);
                            v_isSharedCheck_2563_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2554_)) as u8;
                            if v_isSharedCheck_2563_ == 0 {
                                v___x_2557_ = v___x_2554_;
                                v_isShared_2558_ = v_isSharedCheck_2563_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2555_);
                                crate::leanh::lean_dec(v___x_2554_);
                                v___x_2557_ = crate::leanh::lean_box(0);
                                v_isShared_2558_ = v_isSharedCheck_2563_;
                                state = 8;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2551_);
                            v_a_2564_ = crate::leanh::lean_ctor_get(v___x_2554_, 0);
                            v_isSharedCheck_2571_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2554_)) as u8;
                            if v_isSharedCheck_2571_ == 0 {
                                v___x_2566_ = v___x_2554_;
                                v_isShared_2567_ = v_isSharedCheck_2571_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2564_);
                                crate::leanh::lean_dec(v___x_2554_);
                                v___x_2566_ = crate::leanh::lean_box(0);
                                v_isShared_2567_ = v_isSharedCheck_2571_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2548_);
                        crate::leanh::lean_dec(v_a_2506_);
                        return v___x_2550_;
                    }
                }
            }
            8 => {
                v___x_2559_ = l_Lean_Name_str___override(v_a_2551_, v_a_2555_);
                if v_isShared_2558_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2557_, 0, v___x_2559_);
                    v___x_2561_ = v___x_2557_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2562_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2559_);
                    v___x_2561_ = v_reuseFailAlloc_2562_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2561_;
            }
            10 => {
                if v_isShared_2567_ == 0 {
                    v___x_2569_ = v___x_2566_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2570_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
                    v___x_2569_ = v_reuseFailAlloc_2570_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2569_;
            }
            12 => {
                if v___y_2573_ == 0 {
                    crate::leanh::lean_del_object(v___x_2508_);
                    v___x_2574_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5;
                    v___x_2575_ = lean_name_eq(v_declName_2511_, v___x_2574_);
                    if v___x_2575_ == 0 {
                        v___y_2542_ = v___x_2575_;
                        state = 7;
                        continue;
                    } else {
                        v___x_2576_ = crate::leanh::lean_box(0);
                        v___x_2577_ =
                            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(
                                v___x_2512_,
                                v___x_2576_,
                            );
                        v___y_2542_ = v___x_2577_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2512_);
                    crate::leanh::lean_dec(v_declName_2511_);
                    crate::leanh::lean_dec(v_a_2506_);
                    v___x_2578_ = crate::leanh::lean_box(0);
                    if v_isShared_2509_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2508_, 0, v___x_2578_);
                        v___x_2580_ = v___x_2508_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_2581_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2578_);
                        v___x_2580_ = v_reuseFailAlloc_2581_;
                        state = 13;
                        continue;
                    }
                }
            }
            13 => {
                return v___x_2580_;
            }
            14 => {
                if v_isShared_2591_ == 0 {
                    v___x_2593_ = v___x_2590_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2594_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
                    v___x_2593_ = v_reuseFailAlloc_2594_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2593_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___boxed(
    mut v_e_2596_: *mut crate::leanh::LeanObject,
    mut v_a_2597_: *mut crate::leanh::LeanObject,
    mut v_a_2598_: *mut crate::leanh::LeanObject,
    mut v_a_2599_: *mut crate::leanh::LeanObject,
    mut v_a_2600_: *mut crate::leanh::LeanObject,
    mut v_a_2601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2602_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(
        v_e_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_,
    );
    crate::leanh::lean_dec(v_a_2600_);
    crate::leanh::lean_dec_ref(v_a_2599_);
    crate::leanh::lean_dec(v_a_2598_);
    crate::leanh::lean_dec_ref(v_a_2597_);
    return v_res_2602_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalName___private__1(
    mut v_e_2603_: *mut crate::leanh::LeanObject,
    mut v_a_2604_: *mut crate::leanh::LeanObject,
    mut v_a_2605_: *mut crate::leanh::LeanObject,
    mut v_a_2606_: *mut crate::leanh::LeanObject,
    mut v_a_2607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2609_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(
        v_e_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_,
    );
    return v___x_2609_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalName___private__1___boxed(
    mut v_e_2610_: *mut crate::leanh::LeanObject,
    mut v_a_2611_: *mut crate::leanh::LeanObject,
    mut v_a_2612_: *mut crate::leanh::LeanObject,
    mut v_a_2613_: *mut crate::leanh::LeanObject,
    mut v_a_2614_: *mut crate::leanh::LeanObject,
    mut v_a_2615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2616_ = l_Lean_Meta_instReduceEvalName___private__1(
        v_e_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_,
    );
    crate::leanh::lean_dec(v_a_2614_);
    crate::leanh::lean_dec_ref(v_a_2613_);
    crate::leanh::lean_dec(v_a_2612_);
    crate::leanh::lean_dec_ref(v_a_2611_);
    return v_res_2616_;
}
pub unsafe fn l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(
    mut v_inst_2622_: *mut crate::leanh::LeanObject,
    mut v_e_2623_: *mut crate::leanh::LeanObject,
    mut v_a_2624_: *mut crate::leanh::LeanObject,
    mut v_a_2625_: *mut crate::leanh::LeanObject,
    mut v_a_2626_: *mut crate::leanh::LeanObject,
    mut v_a_2627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2633_: u8 = 0;
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: u8 = 0;
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: u8 = 0;
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: u8 = 0;
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: u8 = 0;
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2666_: u8 = 0;
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2671_: u8 = 0;
    let mut v_a_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2675_: u8 = 0;
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2679_: u8 = 0;
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: u8 = 0;
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2691_: u8 = 0;
    let mut v_a_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2695_: u8 = 0;
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2699_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_2627_);
                crate::leanh::lean_inc_ref(v_a_2626_);
                crate::leanh::lean_inc(v_a_2625_);
                crate::leanh::lean_inc_ref(v_a_2624_);
                v___x_2629_ = lean_whnf(v_e_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
                if crate::leanh::lean_obj_tag(v___x_2629_) == 0 {
                    v_a_2630_ = crate::leanh::lean_ctor_get(v___x_2629_, 0);
                    v_isSharedCheck_2691_ = (!crate::leanh::lean_is_exclusive(v___x_2629_)) as u8;
                    if v_isSharedCheck_2691_ == 0 {
                        v___x_2632_ = v___x_2629_;
                        v_isShared_2633_ = v_isSharedCheck_2691_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2630_);
                        crate::leanh::lean_dec(v___x_2629_);
                        v___x_2632_ = crate::leanh::lean_box(0);
                        v_isShared_2633_ = v_isSharedCheck_2691_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_2622_);
                    v_a_2692_ = crate::leanh::lean_ctor_get(v___x_2629_, 0);
                    v_isSharedCheck_2699_ = (!crate::leanh::lean_is_exclusive(v___x_2629_)) as u8;
                    if v_isSharedCheck_2699_ == 0 {
                        v___x_2694_ = v___x_2629_;
                        v_isShared_2695_ = v_isSharedCheck_2699_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2692_);
                        crate::leanh::lean_dec(v___x_2629_);
                        v___x_2694_ = crate::leanh::lean_box(0);
                        v_isShared_2695_ = v_isSharedCheck_2699_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2634_ = l_Lean_Expr_getAppFn(v_a_2630_);
                if crate::leanh::lean_obj_tag(v___x_2634_) == 4 {
                    v_declName_2635_ = crate::leanh::lean_ctor_get(v___x_2634_, 0);
                    crate::leanh::lean_inc(v_declName_2635_);
                    crate::leanh::lean_dec_ref_known(v___x_2634_, 2);
                    if crate::leanh::lean_obj_tag(v_declName_2635_) == 1 {
                        v_pre_2636_ = crate::leanh::lean_ctor_get(v_declName_2635_, 0);
                        crate::leanh::lean_inc(v_pre_2636_);
                        if crate::leanh::lean_obj_tag(v_pre_2636_) == 1 {
                            v_pre_2637_ = crate::leanh::lean_ctor_get(v_pre_2636_, 0);
                            if crate::leanh::lean_obj_tag(v_pre_2637_) == 0 {
                                v_str_2638_ = crate::leanh::lean_ctor_get(v_declName_2635_, 1);
                                crate::leanh::lean_inc_ref(v_str_2638_);
                                crate::leanh::lean_dec_ref_known(v_declName_2635_, 2);
                                v_str_2639_ = crate::leanh::lean_ctor_get(v_pre_2636_, 1);
                                crate::leanh::lean_inc_ref(v_str_2639_);
                                crate::leanh::lean_dec_ref_known(v_pre_2636_, 2);
                                v___x_2640_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__0;
                                v___x_2641_ = lean_string_dec_eq(v_str_2639_, v___x_2640_);
                                crate::leanh::lean_dec_ref(v_str_2639_);
                                if v___x_2641_ == 0 {
                                    crate::leanh::lean_dec_ref(v_str_2638_);
                                    crate::leanh::lean_del_object(v___x_2632_);
                                    crate::leanh::lean_dec_ref(v_inst_2622_);
                                    v___x_2642_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_2630_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
                                    return v___x_2642_;
                                } else {
                                    v___x_2643_ = l_Lean_Expr_getAppNumArgs(v_a_2630_);
                                    v___x_2644_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__1;
                                    v___x_2645_ = lean_string_dec_eq(v_str_2638_, v___x_2644_);
                                    if v___x_2645_ == 0 {
                                        crate::leanh::lean_del_object(v___x_2632_);
                                        v___x_2646_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__2;
                                        v___x_2647_ = lean_string_dec_eq(v_str_2638_, v___x_2646_);
                                        crate::leanh::lean_dec_ref(v_str_2638_);
                                        if v___x_2647_ == 0 {
                                            crate::leanh::lean_dec(v___x_2643_);
                                            crate::leanh::lean_dec_ref(v_inst_2622_);
                                            v___x_2648_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_2630_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
                                            return v___x_2648_;
                                        } else {
                                            v___x_2649_ = crate::leanh::lean_unsigned_to_nat(3);
                                            v___x_2650_ = lean_nat_dec_eq(v___x_2643_, v___x_2649_);
                                            if v___x_2650_ == 0 {
                                                crate::leanh::lean_dec(v___x_2643_);
                                                crate::leanh::lean_dec_ref(v_inst_2622_);
                                                v___x_2651_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_2630_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
                                                return v___x_2651_;
                                            } else {
                                                v___x_2652_ = crate::leanh::lean_unsigned_to_nat(1);
                                                v___x_2653_ =
                                                    lean_nat_sub(v___x_2643_, v___x_2652_);
                                                v___x_2654_ =
                                                    lean_nat_sub(v___x_2653_, v___x_2652_);
                                                crate::leanh::lean_dec(v___x_2653_);
                                                v___x_2655_ = l_Lean_Expr_getRevArg_x21(
                                                    v_a_2630_,
                                                    v___x_2654_,
                                                );
                                                crate::leanh::lean_inc_ref(v_inst_2622_);
                                                v___x_2656_ = l_Lean_Meta_reduceEval___redArg(
                                                    v_inst_2622_,
                                                    v___x_2655_,
                                                    v_a_2624_,
                                                    v_a_2625_,
                                                    v_a_2626_,
                                                    v_a_2627_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_2656_) == 0 {
                                                    v_a_2657_ =
                                                        crate::leanh::lean_ctor_get(v___x_2656_, 0);
                                                    crate::leanh::lean_inc(v_a_2657_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_2656_,
                                                        1,
                                                    );
                                                    v___x_2658_ =
                                                        crate::leanh::lean_unsigned_to_nat(2);
                                                    v___x_2659_ =
                                                        lean_nat_sub(v___x_2643_, v___x_2658_);
                                                    crate::leanh::lean_dec(v___x_2643_);
                                                    v___x_2660_ =
                                                        lean_nat_sub(v___x_2659_, v___x_2652_);
                                                    crate::leanh::lean_dec(v___x_2659_);
                                                    v___x_2661_ = l_Lean_Expr_getRevArg_x21(
                                                        v_a_2630_,
                                                        v___x_2660_,
                                                    );
                                                    crate::leanh::lean_dec(v_a_2630_);
                                                    v___x_2662_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_2622_, v___x_2661_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
                                                    if crate::leanh::lean_obj_tag(v___x_2662_) == 0
                                                    {
                                                        v_a_2663_ = crate::leanh::lean_ctor_get(
                                                            v___x_2662_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_2671_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_2662_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_2671_ == 0 {
                                                            v___x_2665_ = v___x_2662_;
                                                            v_isShared_2666_ =
                                                                v_isSharedCheck_2671_;
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_2663_);
                                                            crate::leanh::lean_dec(v___x_2662_);
                                                            v___x_2665_ = crate::leanh::lean_box(0);
                                                            v_isShared_2666_ =
                                                                v_isSharedCheck_2671_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec(v_a_2657_);
                                                        return v___x_2662_;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v___x_2643_);
                                                    crate::leanh::lean_dec(v_a_2630_);
                                                    crate::leanh::lean_dec_ref(v_inst_2622_);
                                                    v_a_2672_ =
                                                        crate::leanh::lean_ctor_get(v___x_2656_, 0);
                                                    v_isSharedCheck_2679_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_2656_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_2679_ == 0 {
                                                        v___x_2674_ = v___x_2656_;
                                                        v_isShared_2675_ = v_isSharedCheck_2679_;
                                                        state = 4;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_2672_);
                                                        crate::leanh::lean_dec(v___x_2656_);
                                                        v___x_2674_ = crate::leanh::lean_box(0);
                                                        v_isShared_2675_ = v_isSharedCheck_2679_;
                                                        state = 4;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_str_2638_);
                                        crate::leanh::lean_dec_ref(v_inst_2622_);
                                        v___x_2680_ = crate::leanh::lean_unsigned_to_nat(1);
                                        v___x_2681_ = lean_nat_dec_eq(v___x_2643_, v___x_2680_);
                                        crate::leanh::lean_dec(v___x_2643_);
                                        if v___x_2681_ == 0 {
                                            crate::leanh::lean_del_object(v___x_2632_);
                                            v___x_2682_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_2630_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
                                            return v___x_2682_;
                                        } else {
                                            crate::leanh::lean_dec(v_a_2630_);
                                            v___x_2683_ = crate::leanh::lean_box(0);
                                            if v_isShared_2633_ == 0 {
                                                crate::leanh::lean_ctor_set(
                                                    v___x_2632_,
                                                    0,
                                                    v___x_2683_,
                                                );
                                                v___x_2685_ = v___x_2632_;
                                                state = 6;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_2686_ =
                                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v_reuseFailAlloc_2686_,
                                                    0,
                                                    v___x_2683_,
                                                );
                                                v___x_2685_ = v_reuseFailAlloc_2686_;
                                                state = 6;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_pre_2636_, 2);
                                crate::leanh::lean_dec_ref_known(v_declName_2635_, 2);
                                crate::leanh::lean_del_object(v___x_2632_);
                                crate::leanh::lean_dec_ref(v_inst_2622_);
                                v___x_2687_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_2630_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
                                return v___x_2687_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_pre_2636_);
                            crate::leanh::lean_dec_ref_known(v_declName_2635_, 2);
                            crate::leanh::lean_del_object(v___x_2632_);
                            crate::leanh::lean_dec_ref(v_inst_2622_);
                            v___x_2688_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_2630_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
                            return v___x_2688_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_2635_);
                        crate::leanh::lean_del_object(v___x_2632_);
                        crate::leanh::lean_dec_ref(v_inst_2622_);
                        v___x_2689_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_2630_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
                        return v___x_2689_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2634_);
                    crate::leanh::lean_del_object(v___x_2632_);
                    crate::leanh::lean_dec_ref(v_inst_2622_);
                    v___x_2690_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_a_2630_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_,
                        );
                    return v___x_2690_;
                }
            }
            2 => {
                v___x_2667_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2667_, 0, v_a_2657_);
                crate::leanh::lean_ctor_set(v___x_2667_, 1, v_a_2663_);
                if v_isShared_2666_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2665_, 0, v___x_2667_);
                    v___x_2669_ = v___x_2665_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2670_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2667_);
                    v___x_2669_ = v_reuseFailAlloc_2670_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2669_;
            }
            4 => {
                if v_isShared_2675_ == 0 {
                    v___x_2677_ = v___x_2674_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2678_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
                    v___x_2677_ = v_reuseFailAlloc_2678_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2677_;
            }
            6 => {
                return v___x_2685_;
            }
            7 => {
                if v_isShared_2695_ == 0 {
                    v___x_2697_ = v___x_2694_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2698_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
                    v___x_2697_ = v_reuseFailAlloc_2698_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2697_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___boxed(
    mut v_inst_2700_: *mut crate::leanh::LeanObject,
    mut v_e_2701_: *mut crate::leanh::LeanObject,
    mut v_a_2702_: *mut crate::leanh::LeanObject,
    mut v_a_2703_: *mut crate::leanh::LeanObject,
    mut v_a_2704_: *mut crate::leanh::LeanObject,
    mut v_a_2705_: *mut crate::leanh::LeanObject,
    mut v_a_2706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2707_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(
        v_inst_2700_,
        v_e_2701_,
        v_a_2702_,
        v_a_2703_,
        v_a_2704_,
        v_a_2705_,
    );
    crate::leanh::lean_dec(v_a_2705_);
    crate::leanh::lean_dec_ref(v_a_2704_);
    crate::leanh::lean_dec(v_a_2703_);
    crate::leanh::lean_dec_ref(v_a_2702_);
    return v_res_2707_;
}
pub unsafe fn l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList(
    mut v_00_u03b1_2708_: *mut crate::leanh::LeanObject,
    mut v_inst_2709_: *mut crate::leanh::LeanObject,
    mut v_e_2710_: *mut crate::leanh::LeanObject,
    mut v_a_2711_: *mut crate::leanh::LeanObject,
    mut v_a_2712_: *mut crate::leanh::LeanObject,
    mut v_a_2713_: *mut crate::leanh::LeanObject,
    mut v_a_2714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2716_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(
        v_inst_2709_,
        v_e_2710_,
        v_a_2711_,
        v_a_2712_,
        v_a_2713_,
        v_a_2714_,
    );
    return v___x_2716_;
}
pub unsafe fn l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___boxed(
    mut v_00_u03b1_2717_: *mut crate::leanh::LeanObject,
    mut v_inst_2718_: *mut crate::leanh::LeanObject,
    mut v_e_2719_: *mut crate::leanh::LeanObject,
    mut v_a_2720_: *mut crate::leanh::LeanObject,
    mut v_a_2721_: *mut crate::leanh::LeanObject,
    mut v_a_2722_: *mut crate::leanh::LeanObject,
    mut v_a_2723_: *mut crate::leanh::LeanObject,
    mut v_a_2724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2725_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList(
        v_00_u03b1_2717_,
        v_inst_2718_,
        v_e_2719_,
        v_a_2720_,
        v_a_2721_,
        v_a_2722_,
        v_a_2723_,
    );
    crate::leanh::lean_dec(v_a_2723_);
    crate::leanh::lean_dec_ref(v_a_2722_);
    crate::leanh::lean_dec(v_a_2721_);
    crate::leanh::lean_dec_ref(v_a_2720_);
    return v_res_2725_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalList___private__1___redArg(
    mut v_inst_2726_: *mut crate::leanh::LeanObject,
    mut v_e_2727_: *mut crate::leanh::LeanObject,
    mut v_a_2728_: *mut crate::leanh::LeanObject,
    mut v_a_2729_: *mut crate::leanh::LeanObject,
    mut v_a_2730_: *mut crate::leanh::LeanObject,
    mut v_a_2731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2733_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(
        v_inst_2726_,
        v_e_2727_,
        v_a_2728_,
        v_a_2729_,
        v_a_2730_,
        v_a_2731_,
    );
    return v___x_2733_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalList___private__1___redArg___boxed(
    mut v_inst_2734_: *mut crate::leanh::LeanObject,
    mut v_e_2735_: *mut crate::leanh::LeanObject,
    mut v_a_2736_: *mut crate::leanh::LeanObject,
    mut v_a_2737_: *mut crate::leanh::LeanObject,
    mut v_a_2738_: *mut crate::leanh::LeanObject,
    mut v_a_2739_: *mut crate::leanh::LeanObject,
    mut v_a_2740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2741_ = l_Lean_Meta_instReduceEvalList___private__1___redArg(
        v_inst_2734_,
        v_e_2735_,
        v_a_2736_,
        v_a_2737_,
        v_a_2738_,
        v_a_2739_,
    );
    crate::leanh::lean_dec(v_a_2739_);
    crate::leanh::lean_dec_ref(v_a_2738_);
    crate::leanh::lean_dec(v_a_2737_);
    crate::leanh::lean_dec_ref(v_a_2736_);
    return v_res_2741_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalList___private__1(
    mut v_00_u03b1_2742_: *mut crate::leanh::LeanObject,
    mut v_inst_2743_: *mut crate::leanh::LeanObject,
    mut v_e_2744_: *mut crate::leanh::LeanObject,
    mut v_a_2745_: *mut crate::leanh::LeanObject,
    mut v_a_2746_: *mut crate::leanh::LeanObject,
    mut v_a_2747_: *mut crate::leanh::LeanObject,
    mut v_a_2748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2750_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(
        v_inst_2743_,
        v_e_2744_,
        v_a_2745_,
        v_a_2746_,
        v_a_2747_,
        v_a_2748_,
    );
    return v___x_2750_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalList___private__1___boxed(
    mut v_00_u03b1_2751_: *mut crate::leanh::LeanObject,
    mut v_inst_2752_: *mut crate::leanh::LeanObject,
    mut v_e_2753_: *mut crate::leanh::LeanObject,
    mut v_a_2754_: *mut crate::leanh::LeanObject,
    mut v_a_2755_: *mut crate::leanh::LeanObject,
    mut v_a_2756_: *mut crate::leanh::LeanObject,
    mut v_a_2757_: *mut crate::leanh::LeanObject,
    mut v_a_2758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2759_ = l_Lean_Meta_instReduceEvalList___private__1(
        v_00_u03b1_2751_,
        v_inst_2752_,
        v_e_2753_,
        v_a_2754_,
        v_a_2755_,
        v_a_2756_,
        v_a_2757_,
    );
    crate::leanh::lean_dec(v_a_2757_);
    crate::leanh::lean_dec_ref(v_a_2756_);
    crate::leanh::lean_dec(v_a_2755_);
    crate::leanh::lean_dec_ref(v_a_2754_);
    return v_res_2759_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalList___redArg(
    mut v_inst_2760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2761_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_instReduceEvalList___private__1___boxed as *mut core::ffi::c_void,
        8,
        2,
    );
    crate::leanh::lean_closure_set(v___x_2761_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2761_, 1, v_inst_2760_);
    return v___x_2761_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalList(
    mut v_00_u03b1_2762_: *mut crate::leanh::LeanObject,
    mut v_inst_2763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2764_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_instReduceEvalList___private__1___boxed as *mut core::ffi::c_void,
        8,
        2,
    );
    crate::leanh::lean_closure_set(v___x_2764_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2764_, 1, v_inst_2763_);
    return v___x_2764_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg(
    mut v_n_2770_: *mut crate::leanh::LeanObject,
    mut v_e_2771_: *mut crate::leanh::LeanObject,
    mut v_a_2772_: *mut crate::leanh::LeanObject,
    mut v_a_2773_: *mut crate::leanh::LeanObject,
    mut v_a_2774_: *mut crate::leanh::LeanObject,
    mut v_a_2775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: u8 = 0;
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2793_: u8 = 0;
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2798_: u8 = 0;
    let mut v_a_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2802_: u8 = 0;
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2806_: u8 = 0;
    let mut v_a_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2810_: u8 = 0;
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2814_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_2775_);
                crate::leanh::lean_inc_ref(v_a_2774_);
                crate::leanh::lean_inc(v_a_2773_);
                crate::leanh::lean_inc_ref(v_a_2772_);
                v___x_2777_ = lean_whnf(v_e_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_);
                if crate::leanh::lean_obj_tag(v___x_2777_) == 0 {
                    v_a_2778_ = crate::leanh::lean_ctor_get(v___x_2777_, 0);
                    crate::leanh::lean_inc(v_a_2778_);
                    crate::leanh::lean_dec_ref_known(v___x_2777_, 1);
                    v___x_2779_ =
                        l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2;
                    v___x_2780_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2781_ = l_Lean_Expr_isAppOfArity(v_a_2778_, v___x_2779_, v___x_2780_);
                    if v___x_2781_ == 0 {
                        v___x_2782_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_2778_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_);
                        return v___x_2782_;
                    } else {
                        v___f_2783_ = l_Lean_Meta_instReduceEvalNat___closed__0;
                        v___x_2784_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2785_ = l_Lean_Expr_getAppNumArgs(v_a_2778_);
                        v___x_2786_ = lean_nat_sub(v___x_2785_, v___x_2784_);
                        crate::leanh::lean_dec(v___x_2785_);
                        v___x_2787_ = lean_nat_sub(v___x_2786_, v___x_2784_);
                        crate::leanh::lean_dec(v___x_2786_);
                        v___x_2788_ = l_Lean_Expr_getRevArg_x21(v_a_2778_, v___x_2787_);
                        crate::leanh::lean_dec(v_a_2778_);
                        v___x_2789_ = l_Lean_Meta_reduceEval___redArg(
                            v___f_2783_,
                            v___x_2788_,
                            v_a_2772_,
                            v_a_2773_,
                            v_a_2774_,
                            v_a_2775_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2789_) == 0 {
                            v_a_2790_ = crate::leanh::lean_ctor_get(v___x_2789_, 0);
                            v_isSharedCheck_2798_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2789_)) as u8;
                            if v_isSharedCheck_2798_ == 0 {
                                v___x_2792_ = v___x_2789_;
                                v_isShared_2793_ = v_isSharedCheck_2798_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2790_);
                                crate::leanh::lean_dec(v___x_2789_);
                                v___x_2792_ = crate::leanh::lean_box(0);
                                v_isShared_2793_ = v_isSharedCheck_2798_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_2799_ = crate::leanh::lean_ctor_get(v___x_2789_, 0);
                            v_isSharedCheck_2806_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2789_)) as u8;
                            if v_isSharedCheck_2806_ == 0 {
                                v___x_2801_ = v___x_2789_;
                                v_isShared_2802_ = v_isSharedCheck_2806_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2799_);
                                crate::leanh::lean_dec(v___x_2789_);
                                v___x_2801_ = crate::leanh::lean_box(0);
                                v_isShared_2802_ = v_isSharedCheck_2806_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_2807_ = crate::leanh::lean_ctor_get(v___x_2777_, 0);
                    v_isSharedCheck_2814_ = (!crate::leanh::lean_is_exclusive(v___x_2777_)) as u8;
                    if v_isSharedCheck_2814_ == 0 {
                        v___x_2809_ = v___x_2777_;
                        v_isShared_2810_ = v_isSharedCheck_2814_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2807_);
                        crate::leanh::lean_dec(v___x_2777_);
                        v___x_2809_ = crate::leanh::lean_box(0);
                        v_isShared_2810_ = v_isSharedCheck_2814_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2794_ = lean_nat_mod(v_a_2790_, v_n_2770_);
                crate::leanh::lean_dec(v_a_2790_);
                if v_isShared_2793_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2792_, 0, v___x_2794_);
                    v___x_2796_ = v___x_2792_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2797_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
                    v___x_2796_ = v_reuseFailAlloc_2797_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2796_;
            }
            3 => {
                if v_isShared_2802_ == 0 {
                    v___x_2804_ = v___x_2801_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2805_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
                    v___x_2804_ = v_reuseFailAlloc_2805_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2804_;
            }
            5 => {
                if v_isShared_2810_ == 0 {
                    v___x_2812_ = v___x_2809_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2813_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
                    v___x_2812_ = v_reuseFailAlloc_2813_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2812_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___boxed(
    mut v_n_2815_: *mut crate::leanh::LeanObject,
    mut v_e_2816_: *mut crate::leanh::LeanObject,
    mut v_a_2817_: *mut crate::leanh::LeanObject,
    mut v_a_2818_: *mut crate::leanh::LeanObject,
    mut v_a_2819_: *mut crate::leanh::LeanObject,
    mut v_a_2820_: *mut crate::leanh::LeanObject,
    mut v_a_2821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2822_ = l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg(
        v_n_2815_, v_e_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_,
    );
    crate::leanh::lean_dec(v_a_2820_);
    crate::leanh::lean_dec_ref(v_a_2819_);
    crate::leanh::lean_dec(v_a_2818_);
    crate::leanh::lean_dec_ref(v_a_2817_);
    crate::leanh::lean_dec(v_n_2815_);
    return v_res_2822_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1(
    mut v_n_2823_: *mut crate::leanh::LeanObject,
    mut v_inst_2824_: *mut crate::leanh::LeanObject,
    mut v_e_2825_: *mut crate::leanh::LeanObject,
    mut v_a_2826_: *mut crate::leanh::LeanObject,
    mut v_a_2827_: *mut crate::leanh::LeanObject,
    mut v_a_2828_: *mut crate::leanh::LeanObject,
    mut v_a_2829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: u8 = 0;
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2847_: u8 = 0;
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2852_: u8 = 0;
    let mut v_a_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2856_: u8 = 0;
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2860_: u8 = 0;
    let mut v_a_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2864_: u8 = 0;
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2868_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_2829_);
                crate::leanh::lean_inc_ref(v_a_2828_);
                crate::leanh::lean_inc(v_a_2827_);
                crate::leanh::lean_inc_ref(v_a_2826_);
                v___x_2831_ = lean_whnf(v_e_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_);
                if crate::leanh::lean_obj_tag(v___x_2831_) == 0 {
                    v_a_2832_ = crate::leanh::lean_ctor_get(v___x_2831_, 0);
                    crate::leanh::lean_inc(v_a_2832_);
                    crate::leanh::lean_dec_ref_known(v___x_2831_, 1);
                    v___x_2833_ =
                        l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2;
                    v___x_2834_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2835_ = l_Lean_Expr_isAppOfArity(v_a_2832_, v___x_2833_, v___x_2834_);
                    if v___x_2835_ == 0 {
                        v___x_2836_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_2832_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_);
                        return v___x_2836_;
                    } else {
                        v___f_2837_ = l_Lean_Meta_instReduceEvalNat___closed__0;
                        v___x_2838_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2839_ = l_Lean_Expr_getAppNumArgs(v_a_2832_);
                        v___x_2840_ = lean_nat_sub(v___x_2839_, v___x_2838_);
                        crate::leanh::lean_dec(v___x_2839_);
                        v___x_2841_ = lean_nat_sub(v___x_2840_, v___x_2838_);
                        crate::leanh::lean_dec(v___x_2840_);
                        v___x_2842_ = l_Lean_Expr_getRevArg_x21(v_a_2832_, v___x_2841_);
                        crate::leanh::lean_dec(v_a_2832_);
                        v___x_2843_ = l_Lean_Meta_reduceEval___redArg(
                            v___f_2837_,
                            v___x_2842_,
                            v_a_2826_,
                            v_a_2827_,
                            v_a_2828_,
                            v_a_2829_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2843_) == 0 {
                            v_a_2844_ = crate::leanh::lean_ctor_get(v___x_2843_, 0);
                            v_isSharedCheck_2852_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2843_)) as u8;
                            if v_isSharedCheck_2852_ == 0 {
                                v___x_2846_ = v___x_2843_;
                                v_isShared_2847_ = v_isSharedCheck_2852_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2844_);
                                crate::leanh::lean_dec(v___x_2843_);
                                v___x_2846_ = crate::leanh::lean_box(0);
                                v_isShared_2847_ = v_isSharedCheck_2852_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_2853_ = crate::leanh::lean_ctor_get(v___x_2843_, 0);
                            v_isSharedCheck_2860_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2843_)) as u8;
                            if v_isSharedCheck_2860_ == 0 {
                                v___x_2855_ = v___x_2843_;
                                v_isShared_2856_ = v_isSharedCheck_2860_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2853_);
                                crate::leanh::lean_dec(v___x_2843_);
                                v___x_2855_ = crate::leanh::lean_box(0);
                                v_isShared_2856_ = v_isSharedCheck_2860_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_2861_ = crate::leanh::lean_ctor_get(v___x_2831_, 0);
                    v_isSharedCheck_2868_ = (!crate::leanh::lean_is_exclusive(v___x_2831_)) as u8;
                    if v_isSharedCheck_2868_ == 0 {
                        v___x_2863_ = v___x_2831_;
                        v_isShared_2864_ = v_isSharedCheck_2868_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2861_);
                        crate::leanh::lean_dec(v___x_2831_);
                        v___x_2863_ = crate::leanh::lean_box(0);
                        v_isShared_2864_ = v_isSharedCheck_2868_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2848_ = lean_nat_mod(v_a_2844_, v_n_2823_);
                crate::leanh::lean_dec(v_a_2844_);
                if v_isShared_2847_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2846_, 0, v___x_2848_);
                    v___x_2850_ = v___x_2846_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2851_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2848_);
                    v___x_2850_ = v_reuseFailAlloc_2851_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2850_;
            }
            3 => {
                if v_isShared_2856_ == 0 {
                    v___x_2858_ = v___x_2855_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2859_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
                    v___x_2858_ = v_reuseFailAlloc_2859_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2858_;
            }
            5 => {
                if v_isShared_2864_ == 0 {
                    v___x_2866_ = v___x_2863_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2867_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
                    v___x_2866_ = v_reuseFailAlloc_2867_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2866_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed(
    mut v_n_2869_: *mut crate::leanh::LeanObject,
    mut v_inst_2870_: *mut crate::leanh::LeanObject,
    mut v_e_2871_: *mut crate::leanh::LeanObject,
    mut v_a_2872_: *mut crate::leanh::LeanObject,
    mut v_a_2873_: *mut crate::leanh::LeanObject,
    mut v_a_2874_: *mut crate::leanh::LeanObject,
    mut v_a_2875_: *mut crate::leanh::LeanObject,
    mut v_a_2876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2877_ = l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1(
        v_n_2869_,
        v_inst_2870_,
        v_e_2871_,
        v_a_2872_,
        v_a_2873_,
        v_a_2874_,
        v_a_2875_,
    );
    crate::leanh::lean_dec(v_a_2875_);
    crate::leanh::lean_dec_ref(v_a_2874_);
    crate::leanh::lean_dec(v_a_2873_);
    crate::leanh::lean_dec_ref(v_a_2872_);
    crate::leanh::lean_dec(v_n_2869_);
    return v_res_2877_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalFinOfNeZeroNat___redArg(
    mut v_n_2878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2879_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed as *mut core::ffi::c_void,
        8,
        2,
    );
    crate::leanh::lean_closure_set(v___x_2879_, 0, v_n_2878_);
    crate::leanh::lean_closure_set(v___x_2879_, 1, crate::leanh::lean_box(0));
    return v___x_2879_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalFinOfNeZeroNat(
    mut v_n_2880_: *mut crate::leanh::LeanObject,
    mut v_inst_2881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2882_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed as *mut core::ffi::c_void,
        8,
        2,
    );
    crate::leanh::lean_closure_set(v___x_2882_, 0, v_n_2880_);
    crate::leanh::lean_closure_set(v___x_2882_, 1, crate::leanh::lean_box(0));
    return v___x_2882_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalBitVec___private__1(
    mut v_n_2888_: *mut crate::leanh::LeanObject,
    mut v_e_2889_: *mut crate::leanh::LeanObject,
    mut v_a_2890_: *mut crate::leanh::LeanObject,
    mut v_a_2891_: *mut crate::leanh::LeanObject,
    mut v_a_2892_: *mut crate::leanh::LeanObject,
    mut v_a_2893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: u8 = 0;
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2914_: u8 = 0;
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2918_: u8 = 0;
    let mut v_a_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2922_: u8 = 0;
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2926_: u8 = 0;
    let mut v_a_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2930_: u8 = 0;
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_2893_);
                crate::leanh::lean_inc_ref(v_a_2892_);
                crate::leanh::lean_inc(v_a_2891_);
                crate::leanh::lean_inc_ref(v_a_2890_);
                v___x_2895_ = lean_whnf(v_e_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
                if crate::leanh::lean_obj_tag(v___x_2895_) == 0 {
                    v_a_2896_ = crate::leanh::lean_ctor_get(v___x_2895_, 0);
                    crate::leanh::lean_inc(v_a_2896_);
                    crate::leanh::lean_dec_ref_known(v___x_2895_, 1);
                    v___x_2897_ = l_Lean_Meta_instReduceEvalBitVec___private__1___closed__2;
                    v___x_2898_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_2899_ = l_Lean_Expr_isAppOfArity(v_a_2896_, v___x_2897_, v___x_2898_);
                    if v___x_2899_ == 0 {
                        v___x_2900_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_2896_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
                        return v___x_2900_;
                    } else {
                        v___x_2901_ = lean_nat_pow(v___x_2898_, v_n_2888_);
                        v___x_2902_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2903_ = lean_nat_sub(v___x_2901_, v___x_2902_);
                        crate::leanh::lean_dec(v___x_2901_);
                        v___x_2904_ = lean_nat_add(v___x_2903_, v___x_2902_);
                        crate::leanh::lean_dec(v___x_2903_);
                        v___x_2905_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed
                                as *mut core::ffi::c_void,
                            8,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___x_2905_, 0, v___x_2904_);
                        crate::leanh::lean_closure_set(v___x_2905_, 1, crate::leanh::lean_box(0));
                        v___x_2906_ = l_Lean_Expr_getAppNumArgs(v_a_2896_);
                        v___x_2907_ = lean_nat_sub(v___x_2906_, v___x_2902_);
                        crate::leanh::lean_dec(v___x_2906_);
                        v___x_2908_ = lean_nat_sub(v___x_2907_, v___x_2902_);
                        crate::leanh::lean_dec(v___x_2907_);
                        v___x_2909_ = l_Lean_Expr_getRevArg_x21(v_a_2896_, v___x_2908_);
                        crate::leanh::lean_dec(v_a_2896_);
                        v___x_2910_ = l_Lean_Meta_reduceEval___redArg(
                            v___x_2905_,
                            v___x_2909_,
                            v_a_2890_,
                            v_a_2891_,
                            v_a_2892_,
                            v_a_2893_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2910_) == 0 {
                            v_a_2911_ = crate::leanh::lean_ctor_get(v___x_2910_, 0);
                            v_isSharedCheck_2918_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2910_)) as u8;
                            if v_isSharedCheck_2918_ == 0 {
                                v___x_2913_ = v___x_2910_;
                                v_isShared_2914_ = v_isSharedCheck_2918_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2911_);
                                crate::leanh::lean_dec(v___x_2910_);
                                v___x_2913_ = crate::leanh::lean_box(0);
                                v_isShared_2914_ = v_isSharedCheck_2918_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_2919_ = crate::leanh::lean_ctor_get(v___x_2910_, 0);
                            v_isSharedCheck_2926_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2910_)) as u8;
                            if v_isSharedCheck_2926_ == 0 {
                                v___x_2921_ = v___x_2910_;
                                v_isShared_2922_ = v_isSharedCheck_2926_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2919_);
                                crate::leanh::lean_dec(v___x_2910_);
                                v___x_2921_ = crate::leanh::lean_box(0);
                                v_isShared_2922_ = v_isSharedCheck_2926_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_2927_ = crate::leanh::lean_ctor_get(v___x_2895_, 0);
                    v_isSharedCheck_2934_ = (!crate::leanh::lean_is_exclusive(v___x_2895_)) as u8;
                    if v_isSharedCheck_2934_ == 0 {
                        v___x_2929_ = v___x_2895_;
                        v_isShared_2930_ = v_isSharedCheck_2934_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2927_);
                        crate::leanh::lean_dec(v___x_2895_);
                        v___x_2929_ = crate::leanh::lean_box(0);
                        v_isShared_2930_ = v_isSharedCheck_2934_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2914_ == 0 {
                    v___x_2916_ = v___x_2913_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2917_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
                    v___x_2916_ = v_reuseFailAlloc_2917_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2916_;
            }
            3 => {
                if v_isShared_2922_ == 0 {
                    v___x_2924_ = v___x_2921_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2925_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
                    v___x_2924_ = v_reuseFailAlloc_2925_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2924_;
            }
            5 => {
                if v_isShared_2930_ == 0 {
                    v___x_2932_ = v___x_2929_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2933_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
                    v___x_2932_ = v_reuseFailAlloc_2933_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2932_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instReduceEvalBitVec___private__1___boxed(
    mut v_n_2935_: *mut crate::leanh::LeanObject,
    mut v_e_2936_: *mut crate::leanh::LeanObject,
    mut v_a_2937_: *mut crate::leanh::LeanObject,
    mut v_a_2938_: *mut crate::leanh::LeanObject,
    mut v_a_2939_: *mut crate::leanh::LeanObject,
    mut v_a_2940_: *mut crate::leanh::LeanObject,
    mut v_a_2941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2942_ = l_Lean_Meta_instReduceEvalBitVec___private__1(
        v_n_2935_, v_e_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_,
    );
    crate::leanh::lean_dec(v_a_2940_);
    crate::leanh::lean_dec_ref(v_a_2939_);
    crate::leanh::lean_dec(v_a_2938_);
    crate::leanh::lean_dec_ref(v_a_2937_);
    crate::leanh::lean_dec(v_n_2935_);
    return v_res_2942_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalBitVec(
    mut v_n_2943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2944_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_instReduceEvalBitVec___private__1___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    crate::leanh::lean_closure_set(v___x_2944_, 0, v_n_2943_);
    return v___x_2944_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalBool___private__1(
    mut v_e_2954_: *mut crate::leanh::LeanObject,
    mut v_a_2955_: *mut crate::leanh::LeanObject,
    mut v_a_2956_: *mut crate::leanh::LeanObject,
    mut v_a_2957_: *mut crate::leanh::LeanObject,
    mut v_a_2958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2964_: u8 = 0;
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: u8 = 0;
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: u8 = 0;
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2978_: u8 = 0;
    let mut v_a_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2982_: u8 = 0;
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_2958_);
                crate::leanh::lean_inc_ref(v_a_2957_);
                crate::leanh::lean_inc(v_a_2956_);
                crate::leanh::lean_inc_ref(v_a_2955_);
                v___x_2960_ = lean_whnf(v_e_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_);
                if crate::leanh::lean_obj_tag(v___x_2960_) == 0 {
                    v_a_2961_ = crate::leanh::lean_ctor_get(v___x_2960_, 0);
                    v_isSharedCheck_2978_ = (!crate::leanh::lean_is_exclusive(v___x_2960_)) as u8;
                    if v_isSharedCheck_2978_ == 0 {
                        v___x_2963_ = v___x_2960_;
                        v_isShared_2964_ = v_isSharedCheck_2978_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2961_);
                        crate::leanh::lean_dec(v___x_2960_);
                        v___x_2963_ = crate::leanh::lean_box(0);
                        v_isShared_2964_ = v_isSharedCheck_2978_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2979_ = crate::leanh::lean_ctor_get(v___x_2960_, 0);
                    v_isSharedCheck_2986_ = (!crate::leanh::lean_is_exclusive(v___x_2960_)) as u8;
                    if v_isSharedCheck_2986_ == 0 {
                        v___x_2981_ = v___x_2960_;
                        v_isShared_2982_ = v_isSharedCheck_2986_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2979_);
                        crate::leanh::lean_dec(v___x_2960_);
                        v___x_2981_ = crate::leanh::lean_box(0);
                        v_isShared_2982_ = v_isSharedCheck_2986_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2965_ = l_Lean_Meta_instReduceEvalBool___private__1___closed__2;
                v___x_2966_ = l_Lean_Expr_isAppOf(v_a_2961_, v___x_2965_);
                if v___x_2966_ == 0 {
                    v___x_2967_ = l_Lean_Meta_instReduceEvalBool___private__1___closed__4;
                    v___x_2968_ = l_Lean_Expr_isAppOf(v_a_2961_, v___x_2967_);
                    if v___x_2968_ == 0 {
                        crate::leanh::lean_del_object(v___x_2963_);
                        v___x_2969_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_2961_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_);
                        return v___x_2969_;
                    } else {
                        crate::leanh::lean_dec(v_a_2961_);
                        v___x_2970_ = crate::leanh::lean_box((v___x_2966_) as usize);
                        if v_isShared_2964_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2963_, 0, v___x_2970_);
                            v___x_2972_ = v___x_2963_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2973_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2970_);
                            v___x_2972_ = v_reuseFailAlloc_2973_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2961_);
                    v___x_2974_ = crate::leanh::lean_box((v___x_2966_) as usize);
                    if v_isShared_2964_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2963_, 0, v___x_2974_);
                        v___x_2976_ = v___x_2963_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2977_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2974_);
                        v___x_2976_ = v_reuseFailAlloc_2977_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2972_;
            }
            3 => {
                return v___x_2976_;
            }
            4 => {
                if v_isShared_2982_ == 0 {
                    v___x_2984_ = v___x_2981_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2985_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
                    v___x_2984_ = v_reuseFailAlloc_2985_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2984_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instReduceEvalBool___private__1___boxed(
    mut v_e_2987_: *mut crate::leanh::LeanObject,
    mut v_a_2988_: *mut crate::leanh::LeanObject,
    mut v_a_2989_: *mut crate::leanh::LeanObject,
    mut v_a_2990_: *mut crate::leanh::LeanObject,
    mut v_a_2991_: *mut crate::leanh::LeanObject,
    mut v_a_2992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2993_ = l_Lean_Meta_instReduceEvalBool___private__1(
        v_e_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_,
    );
    crate::leanh::lean_dec(v_a_2991_);
    crate::leanh::lean_dec_ref(v_a_2990_);
    crate::leanh::lean_dec(v_a_2989_);
    crate::leanh::lean_dec_ref(v_a_2988_);
    return v_res_2993_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalBinderInfo___private__1(
    mut v_e_3001_: *mut crate::leanh::LeanObject,
    mut v_a_3002_: *mut crate::leanh::LeanObject,
    mut v_a_3003_: *mut crate::leanh::LeanObject,
    mut v_a_3004_: *mut crate::leanh::LeanObject,
    mut v_a_3005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3011_: u8 = 0;
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: u8 = 0;
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: u8 = 0;
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: u8 = 0;
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: u8 = 0;
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: u8 = 0;
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: u8 = 0;
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: u8 = 0;
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: u8 = 0;
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: u8 = 0;
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: u8 = 0;
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3060_: u8 = 0;
    let mut v_a_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3064_: u8 = 0;
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_3005_);
                crate::leanh::lean_inc_ref(v_a_3004_);
                crate::leanh::lean_inc(v_a_3003_);
                crate::leanh::lean_inc_ref(v_a_3002_);
                crate::leanh::lean_inc_ref(v_e_3001_);
                v___x_3007_ = lean_whnf(v_e_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
                if crate::leanh::lean_obj_tag(v___x_3007_) == 0 {
                    v_a_3008_ = crate::leanh::lean_ctor_get(v___x_3007_, 0);
                    v_isSharedCheck_3060_ = (!crate::leanh::lean_is_exclusive(v___x_3007_)) as u8;
                    if v_isSharedCheck_3060_ == 0 {
                        v___x_3010_ = v___x_3007_;
                        v_isShared_3011_ = v_isSharedCheck_3060_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3008_);
                        crate::leanh::lean_dec(v___x_3007_);
                        v___x_3010_ = crate::leanh::lean_box(0);
                        v_isShared_3011_ = v_isSharedCheck_3060_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_3001_);
                    v_a_3061_ = crate::leanh::lean_ctor_get(v___x_3007_, 0);
                    v_isSharedCheck_3068_ = (!crate::leanh::lean_is_exclusive(v___x_3007_)) as u8;
                    if v_isSharedCheck_3068_ == 0 {
                        v___x_3063_ = v___x_3007_;
                        v_isShared_3064_ = v_isSharedCheck_3068_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3061_);
                        crate::leanh::lean_dec(v___x_3007_);
                        v___x_3063_ = crate::leanh::lean_box(0);
                        v_isShared_3064_ = v_isSharedCheck_3068_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3012_ = l_Lean_Expr_constName_x3f(v_a_3008_);
                crate::leanh::lean_dec(v_a_3008_);
                if crate::leanh::lean_obj_tag(v___x_3012_) == 1 {
                    v_val_3013_ = crate::leanh::lean_ctor_get(v___x_3012_, 0);
                    crate::leanh::lean_inc(v_val_3013_);
                    crate::leanh::lean_dec_ref_known(v___x_3012_, 1);
                    if crate::leanh::lean_obj_tag(v_val_3013_) == 1 {
                        v_pre_3014_ = crate::leanh::lean_ctor_get(v_val_3013_, 0);
                        crate::leanh::lean_inc(v_pre_3014_);
                        if crate::leanh::lean_obj_tag(v_pre_3014_) == 1 {
                            v_pre_3015_ = crate::leanh::lean_ctor_get(v_pre_3014_, 0);
                            crate::leanh::lean_inc(v_pre_3015_);
                            if crate::leanh::lean_obj_tag(v_pre_3015_) == 1 {
                                v_pre_3016_ = crate::leanh::lean_ctor_get(v_pre_3015_, 0);
                                if crate::leanh::lean_obj_tag(v_pre_3016_) == 0 {
                                    v_str_3017_ = crate::leanh::lean_ctor_get(v_val_3013_, 1);
                                    crate::leanh::lean_inc_ref(v_str_3017_);
                                    crate::leanh::lean_dec_ref_known(v_val_3013_, 2);
                                    v_str_3018_ = crate::leanh::lean_ctor_get(v_pre_3014_, 1);
                                    crate::leanh::lean_inc_ref(v_str_3018_);
                                    crate::leanh::lean_dec_ref_known(v_pre_3014_, 2);
                                    v_str_3019_ = crate::leanh::lean_ctor_get(v_pre_3015_, 1);
                                    crate::leanh::lean_inc_ref(v_str_3019_);
                                    crate::leanh::lean_dec_ref_known(v_pre_3015_, 2);
                                    v___x_3020_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0;
                                    v___x_3021_ = lean_string_dec_eq(v_str_3019_, v___x_3020_);
                                    crate::leanh::lean_dec_ref(v_str_3019_);
                                    if v___x_3021_ == 0 {
                                        crate::leanh::lean_dec_ref(v_str_3018_);
                                        crate::leanh::lean_dec_ref(v_str_3017_);
                                        crate::leanh::lean_del_object(v___x_3010_);
                                        v___x_3022_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
                                        return v___x_3022_;
                                    } else {
                                        v___x_3023_ = l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__0;
                                        v___x_3024_ = lean_string_dec_eq(v_str_3018_, v___x_3023_);
                                        crate::leanh::lean_dec_ref(v_str_3018_);
                                        if v___x_3024_ == 0 {
                                            crate::leanh::lean_dec_ref(v_str_3017_);
                                            crate::leanh::lean_del_object(v___x_3010_);
                                            v___x_3025_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
                                            return v___x_3025_;
                                        } else {
                                            v___x_3026_ = l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__1;
                                            v___x_3027_ =
                                                lean_string_dec_eq(v_str_3017_, v___x_3026_);
                                            if v___x_3027_ == 0 {
                                                v___x_3028_ = l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__2;
                                                v___x_3029_ =
                                                    lean_string_dec_eq(v_str_3017_, v___x_3028_);
                                                if v___x_3029_ == 0 {
                                                    v___x_3030_ = l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__3;
                                                    v___x_3031_ = lean_string_dec_eq(
                                                        v_str_3017_,
                                                        v___x_3030_,
                                                    );
                                                    if v___x_3031_ == 0 {
                                                        v___x_3032_ = l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__4;
                                                        v___x_3033_ = lean_string_dec_eq(
                                                            v_str_3017_,
                                                            v___x_3032_,
                                                        );
                                                        crate::leanh::lean_dec_ref(v_str_3017_);
                                                        if v___x_3033_ == 0 {
                                                            crate::leanh::lean_del_object(
                                                                v___x_3010_,
                                                            );
                                                            v___x_3034_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
                                                            return v___x_3034_;
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v_e_3001_);
                                                            v___x_3035_ = 3;
                                                            v___x_3036_ = crate::leanh::lean_box(
                                                                (v___x_3035_) as usize,
                                                            );
                                                            if v_isShared_3011_ == 0 {
                                                                crate::leanh::lean_ctor_set(
                                                                    v___x_3010_,
                                                                    0,
                                                                    v___x_3036_,
                                                                );
                                                                v___x_3038_ = v___x_3010_;
                                                                state = 2;
                                                                continue;
                                                            } else {
                                                                v_reuseFailAlloc_3039_ =
                                                                    crate::leanh::lean_alloc_ctor(
                                                                        0,
                                                                        1,
                                                                        (0) as u32,
                                                                    );
                                                                crate::leanh::lean_ctor_set(
                                                                    v_reuseFailAlloc_3039_,
                                                                    0,
                                                                    v___x_3036_,
                                                                );
                                                                v___x_3038_ =
                                                                    v_reuseFailAlloc_3039_;
                                                                state = 2;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v_str_3017_);
                                                        crate::leanh::lean_dec_ref(v_e_3001_);
                                                        v___x_3040_ = 2;
                                                        v___x_3041_ = crate::leanh::lean_box(
                                                            (v___x_3040_) as usize,
                                                        );
                                                        if v_isShared_3011_ == 0 {
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_3010_,
                                                                0,
                                                                v___x_3041_,
                                                            );
                                                            v___x_3043_ = v___x_3010_;
                                                            state = 3;
                                                            continue;
                                                        } else {
                                                            v_reuseFailAlloc_3044_ =
                                                                crate::leanh::lean_alloc_ctor(
                                                                    0,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                            crate::leanh::lean_ctor_set(
                                                                v_reuseFailAlloc_3044_,
                                                                0,
                                                                v___x_3041_,
                                                            );
                                                            v___x_3043_ = v_reuseFailAlloc_3044_;
                                                            state = 3;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_str_3017_);
                                                    crate::leanh::lean_dec_ref(v_e_3001_);
                                                    v___x_3045_ = 1;
                                                    v___x_3046_ = crate::leanh::lean_box(
                                                        (v___x_3045_) as usize,
                                                    );
                                                    if v_isShared_3011_ == 0 {
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_3010_,
                                                            0,
                                                            v___x_3046_,
                                                        );
                                                        v___x_3048_ = v___x_3010_;
                                                        state = 4;
                                                        continue;
                                                    } else {
                                                        v_reuseFailAlloc_3049_ =
                                                            crate::leanh::lean_alloc_ctor(
                                                                0,
                                                                1,
                                                                (0) as u32,
                                                            );
                                                        crate::leanh::lean_ctor_set(
                                                            v_reuseFailAlloc_3049_,
                                                            0,
                                                            v___x_3046_,
                                                        );
                                                        v___x_3048_ = v_reuseFailAlloc_3049_;
                                                        state = 4;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v_str_3017_);
                                                crate::leanh::lean_dec_ref(v_e_3001_);
                                                v___x_3050_ = 0;
                                                v___x_3051_ =
                                                    crate::leanh::lean_box((v___x_3050_) as usize);
                                                if v_isShared_3011_ == 0 {
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3010_,
                                                        0,
                                                        v___x_3051_,
                                                    );
                                                    v___x_3053_ = v___x_3010_;
                                                    state = 5;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_3054_ =
                                                        crate::leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                    crate::leanh::lean_ctor_set(
                                                        v_reuseFailAlloc_3054_,
                                                        0,
                                                        v___x_3051_,
                                                    );
                                                    v___x_3053_ = v_reuseFailAlloc_3054_;
                                                    state = 5;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref_known(v_pre_3015_, 2);
                                    crate::leanh::lean_dec_ref_known(v_pre_3014_, 2);
                                    crate::leanh::lean_dec_ref_known(v_val_3013_, 2);
                                    crate::leanh::lean_del_object(v___x_3010_);
                                    v___x_3055_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
                                    return v___x_3055_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_pre_3014_, 2);
                                crate::leanh::lean_dec(v_pre_3015_);
                                crate::leanh::lean_dec_ref_known(v_val_3013_, 2);
                                crate::leanh::lean_del_object(v___x_3010_);
                                v___x_3056_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
                                return v___x_3056_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_pre_3014_);
                            crate::leanh::lean_dec_ref_known(v_val_3013_, 2);
                            crate::leanh::lean_del_object(v___x_3010_);
                            v___x_3057_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
                            return v___x_3057_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_3013_);
                        crate::leanh::lean_del_object(v___x_3010_);
                        v___x_3058_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
                        return v___x_3058_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3012_);
                    crate::leanh::lean_del_object(v___x_3010_);
                    v___x_3059_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_e_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_,
                        );
                    return v___x_3059_;
                }
            }
            2 => {
                return v___x_3038_;
            }
            3 => {
                return v___x_3043_;
            }
            4 => {
                return v___x_3048_;
            }
            5 => {
                return v___x_3053_;
            }
            6 => {
                if v_isShared_3064_ == 0 {
                    v___x_3066_ = v___x_3063_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3067_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
                    v___x_3066_ = v_reuseFailAlloc_3067_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3066_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instReduceEvalBinderInfo___private__1___boxed(
    mut v_e_3069_: *mut crate::leanh::LeanObject,
    mut v_a_3070_: *mut crate::leanh::LeanObject,
    mut v_a_3071_: *mut crate::leanh::LeanObject,
    mut v_a_3072_: *mut crate::leanh::LeanObject,
    mut v_a_3073_: *mut crate::leanh::LeanObject,
    mut v_a_3074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3075_ = l_Lean_Meta_instReduceEvalBinderInfo___private__1(
        v_e_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_,
    );
    crate::leanh::lean_dec(v_a_3073_);
    crate::leanh::lean_dec_ref(v_a_3072_);
    crate::leanh::lean_dec(v_a_3071_);
    crate::leanh::lean_dec_ref(v_a_3070_);
    return v_res_3075_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalLiteral___private__1(
    mut v_e_3089_: *mut crate::leanh::LeanObject,
    mut v_a_3090_: *mut crate::leanh::LeanObject,
    mut v_a_3091_: *mut crate::leanh::LeanObject,
    mut v_a_3092_: *mut crate::leanh::LeanObject,
    mut v_a_3093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: u8 = 0;
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: u8 = 0;
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3111_: u8 = 0;
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3116_: u8 = 0;
    let mut v_a_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3120_: u8 = 0;
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3124_: u8 = 0;
    let mut v___f_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3133_: u8 = 0;
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3138_: u8 = 0;
    let mut v_a_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3142_: u8 = 0;
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3146_: u8 = 0;
    let mut v_a_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3150_: u8 = 0;
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3154_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_3093_);
                crate::leanh::lean_inc_ref(v_a_3092_);
                crate::leanh::lean_inc(v_a_3091_);
                crate::leanh::lean_inc_ref(v_a_3090_);
                v___x_3095_ = lean_whnf(v_e_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
                if crate::leanh::lean_obj_tag(v___x_3095_) == 0 {
                    v_a_3096_ = crate::leanh::lean_ctor_get(v___x_3095_, 0);
                    crate::leanh::lean_inc(v_a_3096_);
                    crate::leanh::lean_dec_ref_known(v___x_3095_, 1);
                    v___x_3097_ = l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2;
                    v___x_3098_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3099_ = l_Lean_Expr_isAppOfArity(v_a_3096_, v___x_3097_, v___x_3098_);
                    if v___x_3099_ == 0 {
                        v___x_3100_ = l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4;
                        v___x_3101_ = l_Lean_Expr_isAppOfArity(v_a_3096_, v___x_3100_, v___x_3098_);
                        if v___x_3101_ == 0 {
                            v___x_3102_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_3096_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
                            return v___x_3102_;
                        } else {
                            v___f_3103_ = l_Lean_Meta_instReduceEvalString___closed__0;
                            v___x_3104_ = l_Lean_Expr_getAppNumArgs(v_a_3096_);
                            v___x_3105_ = lean_nat_sub(v___x_3104_, v___x_3098_);
                            crate::leanh::lean_dec(v___x_3104_);
                            v___x_3106_ = l_Lean_Expr_getRevArg_x21(v_a_3096_, v___x_3105_);
                            crate::leanh::lean_dec(v_a_3096_);
                            v___x_3107_ = l_Lean_Meta_reduceEval___redArg(
                                v___f_3103_,
                                v___x_3106_,
                                v_a_3090_,
                                v_a_3091_,
                                v_a_3092_,
                                v_a_3093_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3107_) == 0 {
                                v_a_3108_ = crate::leanh::lean_ctor_get(v___x_3107_, 0);
                                v_isSharedCheck_3116_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3107_)) as u8;
                                if v_isSharedCheck_3116_ == 0 {
                                    v___x_3110_ = v___x_3107_;
                                    v_isShared_3111_ = v_isSharedCheck_3116_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3108_);
                                    crate::leanh::lean_dec(v___x_3107_);
                                    v___x_3110_ = crate::leanh::lean_box(0);
                                    v_isShared_3111_ = v_isSharedCheck_3116_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_3117_ = crate::leanh::lean_ctor_get(v___x_3107_, 0);
                                v_isSharedCheck_3124_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3107_)) as u8;
                                if v_isSharedCheck_3124_ == 0 {
                                    v___x_3119_ = v___x_3107_;
                                    v_isShared_3120_ = v_isSharedCheck_3124_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3117_);
                                    crate::leanh::lean_dec(v___x_3107_);
                                    v___x_3119_ = crate::leanh::lean_box(0);
                                    v_isShared_3120_ = v_isSharedCheck_3124_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___f_3125_ = l_Lean_Meta_instReduceEvalNat___closed__0;
                        v___x_3126_ = l_Lean_Expr_getAppNumArgs(v_a_3096_);
                        v___x_3127_ = lean_nat_sub(v___x_3126_, v___x_3098_);
                        crate::leanh::lean_dec(v___x_3126_);
                        v___x_3128_ = l_Lean_Expr_getRevArg_x21(v_a_3096_, v___x_3127_);
                        crate::leanh::lean_dec(v_a_3096_);
                        v___x_3129_ = l_Lean_Meta_reduceEval___redArg(
                            v___f_3125_,
                            v___x_3128_,
                            v_a_3090_,
                            v_a_3091_,
                            v_a_3092_,
                            v_a_3093_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3129_) == 0 {
                            v_a_3130_ = crate::leanh::lean_ctor_get(v___x_3129_, 0);
                            v_isSharedCheck_3138_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3129_)) as u8;
                            if v_isSharedCheck_3138_ == 0 {
                                v___x_3132_ = v___x_3129_;
                                v_isShared_3133_ = v_isSharedCheck_3138_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3130_);
                                crate::leanh::lean_dec(v___x_3129_);
                                v___x_3132_ = crate::leanh::lean_box(0);
                                v_isShared_3133_ = v_isSharedCheck_3138_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v_a_3139_ = crate::leanh::lean_ctor_get(v___x_3129_, 0);
                            v_isSharedCheck_3146_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3129_)) as u8;
                            if v_isSharedCheck_3146_ == 0 {
                                v___x_3141_ = v___x_3129_;
                                v_isShared_3142_ = v_isSharedCheck_3146_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3139_);
                                crate::leanh::lean_dec(v___x_3129_);
                                v___x_3141_ = crate::leanh::lean_box(0);
                                v_isShared_3142_ = v_isSharedCheck_3146_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_3147_ = crate::leanh::lean_ctor_get(v___x_3095_, 0);
                    v_isSharedCheck_3154_ = (!crate::leanh::lean_is_exclusive(v___x_3095_)) as u8;
                    if v_isSharedCheck_3154_ == 0 {
                        v___x_3149_ = v___x_3095_;
                        v_isShared_3150_ = v_isSharedCheck_3154_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3147_);
                        crate::leanh::lean_dec(v___x_3095_);
                        v___x_3149_ = crate::leanh::lean_box(0);
                        v_isShared_3150_ = v_isSharedCheck_3154_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3112_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3112_, 0, v_a_3108_);
                if v_isShared_3111_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3110_, 0, v___x_3112_);
                    v___x_3114_ = v___x_3110_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3115_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3112_);
                    v___x_3114_ = v_reuseFailAlloc_3115_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3114_;
            }
            3 => {
                if v_isShared_3120_ == 0 {
                    v___x_3122_ = v___x_3119_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3123_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
                    v___x_3122_ = v_reuseFailAlloc_3123_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3122_;
            }
            5 => {
                v___x_3134_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3134_, 0, v_a_3130_);
                if v_isShared_3133_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3132_, 0, v___x_3134_);
                    v___x_3136_ = v___x_3132_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3137_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3134_);
                    v___x_3136_ = v_reuseFailAlloc_3137_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3136_;
            }
            7 => {
                if v_isShared_3142_ == 0 {
                    v___x_3144_ = v___x_3141_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3145_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
                    v___x_3144_ = v_reuseFailAlloc_3145_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3144_;
            }
            9 => {
                if v_isShared_3150_ == 0 {
                    v___x_3152_ = v___x_3149_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3153_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
                    v___x_3152_ = v_reuseFailAlloc_3153_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3152_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instReduceEvalLiteral___private__1___boxed(
    mut v_e_3155_: *mut crate::leanh::LeanObject,
    mut v_a_3156_: *mut crate::leanh::LeanObject,
    mut v_a_3157_: *mut crate::leanh::LeanObject,
    mut v_a_3158_: *mut crate::leanh::LeanObject,
    mut v_a_3159_: *mut crate::leanh::LeanObject,
    mut v_a_3160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3161_ = l_Lean_Meta_instReduceEvalLiteral___private__1(
        v_e_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_,
    );
    crate::leanh::lean_dec(v_a_3159_);
    crate::leanh::lean_dec_ref(v_a_3158_);
    crate::leanh::lean_dec(v_a_3157_);
    crate::leanh::lean_dec_ref(v_a_3156_);
    return v_res_3161_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalMVarId___private__1(
    mut v_e_3169_: *mut crate::leanh::LeanObject,
    mut v_a_3170_: *mut crate::leanh::LeanObject,
    mut v_a_3171_: *mut crate::leanh::LeanObject,
    mut v_a_3172_: *mut crate::leanh::LeanObject,
    mut v_a_3173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: u8 = 0;
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3189_: u8 = 0;
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3193_: u8 = 0;
    let mut v_a_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3197_: u8 = 0;
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3201_: u8 = 0;
    let mut v_a_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3205_: u8 = 0;
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3209_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_3173_);
                crate::leanh::lean_inc_ref(v_a_3172_);
                crate::leanh::lean_inc(v_a_3171_);
                crate::leanh::lean_inc_ref(v_a_3170_);
                v___x_3175_ = lean_whnf(v_e_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_);
                if crate::leanh::lean_obj_tag(v___x_3175_) == 0 {
                    v_a_3176_ = crate::leanh::lean_ctor_get(v___x_3175_, 0);
                    crate::leanh::lean_inc(v_a_3176_);
                    crate::leanh::lean_dec_ref_known(v___x_3175_, 1);
                    v___x_3177_ = l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1;
                    v___x_3178_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3179_ = l_Lean_Expr_isAppOfArity(v_a_3176_, v___x_3177_, v___x_3178_);
                    if v___x_3179_ == 0 {
                        v___x_3180_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_3176_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_);
                        return v___x_3180_;
                    } else {
                        v___x_3181_ = l_Lean_Meta_instReduceEvalName___closed__0;
                        v___x_3182_ = l_Lean_Expr_getAppNumArgs(v_a_3176_);
                        v___x_3183_ = lean_nat_sub(v___x_3182_, v___x_3178_);
                        crate::leanh::lean_dec(v___x_3182_);
                        v___x_3184_ = l_Lean_Expr_getRevArg_x21(v_a_3176_, v___x_3183_);
                        crate::leanh::lean_dec(v_a_3176_);
                        v___x_3185_ = l_Lean_Meta_reduceEval___redArg(
                            v___x_3181_,
                            v___x_3184_,
                            v_a_3170_,
                            v_a_3171_,
                            v_a_3172_,
                            v_a_3173_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3185_) == 0 {
                            v_a_3186_ = crate::leanh::lean_ctor_get(v___x_3185_, 0);
                            v_isSharedCheck_3193_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3185_)) as u8;
                            if v_isSharedCheck_3193_ == 0 {
                                v___x_3188_ = v___x_3185_;
                                v_isShared_3189_ = v_isSharedCheck_3193_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3186_);
                                crate::leanh::lean_dec(v___x_3185_);
                                v___x_3188_ = crate::leanh::lean_box(0);
                                v_isShared_3189_ = v_isSharedCheck_3193_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_3194_ = crate::leanh::lean_ctor_get(v___x_3185_, 0);
                            v_isSharedCheck_3201_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3185_)) as u8;
                            if v_isSharedCheck_3201_ == 0 {
                                v___x_3196_ = v___x_3185_;
                                v_isShared_3197_ = v_isSharedCheck_3201_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3194_);
                                crate::leanh::lean_dec(v___x_3185_);
                                v___x_3196_ = crate::leanh::lean_box(0);
                                v_isShared_3197_ = v_isSharedCheck_3201_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_3202_ = crate::leanh::lean_ctor_get(v___x_3175_, 0);
                    v_isSharedCheck_3209_ = (!crate::leanh::lean_is_exclusive(v___x_3175_)) as u8;
                    if v_isSharedCheck_3209_ == 0 {
                        v___x_3204_ = v___x_3175_;
                        v_isShared_3205_ = v_isSharedCheck_3209_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3202_);
                        crate::leanh::lean_dec(v___x_3175_);
                        v___x_3204_ = crate::leanh::lean_box(0);
                        v_isShared_3205_ = v_isSharedCheck_3209_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3189_ == 0 {
                    v___x_3191_ = v___x_3188_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3192_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3186_);
                    v___x_3191_ = v_reuseFailAlloc_3192_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3191_;
            }
            3 => {
                if v_isShared_3197_ == 0 {
                    v___x_3199_ = v___x_3196_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3200_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
                    v___x_3199_ = v_reuseFailAlloc_3200_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3199_;
            }
            5 => {
                if v_isShared_3205_ == 0 {
                    v___x_3207_ = v___x_3204_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3208_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
                    v___x_3207_ = v_reuseFailAlloc_3208_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3207_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instReduceEvalMVarId___private__1___boxed(
    mut v_e_3210_: *mut crate::leanh::LeanObject,
    mut v_a_3211_: *mut crate::leanh::LeanObject,
    mut v_a_3212_: *mut crate::leanh::LeanObject,
    mut v_a_3213_: *mut crate::leanh::LeanObject,
    mut v_a_3214_: *mut crate::leanh::LeanObject,
    mut v_a_3215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3216_ = l_Lean_Meta_instReduceEvalMVarId___private__1(
        v_e_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_,
    );
    crate::leanh::lean_dec(v_a_3214_);
    crate::leanh::lean_dec_ref(v_a_3213_);
    crate::leanh::lean_dec(v_a_3212_);
    crate::leanh::lean_dec_ref(v_a_3211_);
    return v_res_3216_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalMVarId___lam__0(
    mut v_e_3217_: *mut crate::leanh::LeanObject,
    mut v___y_3218_: *mut crate::leanh::LeanObject,
    mut v___y_3219_: *mut crate::leanh::LeanObject,
    mut v___y_3220_: *mut crate::leanh::LeanObject,
    mut v___y_3221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: u8 = 0;
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3237_: u8 = 0;
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3241_: u8 = 0;
    let mut v_a_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3245_: u8 = 0;
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3249_: u8 = 0;
    let mut v_a_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3253_: u8 = 0;
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3257_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_3221_);
                crate::leanh::lean_inc_ref(v___y_3220_);
                crate::leanh::lean_inc(v___y_3219_);
                crate::leanh::lean_inc_ref(v___y_3218_);
                v___x_3223_ = lean_whnf(
                    v_e_3217_,
                    v___y_3218_,
                    v___y_3219_,
                    v___y_3220_,
                    v___y_3221_,
                );
                if crate::leanh::lean_obj_tag(v___x_3223_) == 0 {
                    v_a_3224_ = crate::leanh::lean_ctor_get(v___x_3223_, 0);
                    crate::leanh::lean_inc(v_a_3224_);
                    crate::leanh::lean_dec_ref_known(v___x_3223_, 1);
                    v___x_3225_ = l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1;
                    v___x_3226_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3227_ = l_Lean_Expr_isAppOfArity(v_a_3224_, v___x_3225_, v___x_3226_);
                    if v___x_3227_ == 0 {
                        v___x_3228_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_3224_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
                        return v___x_3228_;
                    } else {
                        v___x_3229_ = l_Lean_Meta_instReduceEvalName___closed__0;
                        v___x_3230_ = l_Lean_Expr_getAppNumArgs(v_a_3224_);
                        v___x_3231_ = lean_nat_sub(v___x_3230_, v___x_3226_);
                        crate::leanh::lean_dec(v___x_3230_);
                        v___x_3232_ = l_Lean_Expr_getRevArg_x21(v_a_3224_, v___x_3231_);
                        crate::leanh::lean_dec(v_a_3224_);
                        v___x_3233_ = l_Lean_Meta_reduceEval___redArg(
                            v___x_3229_,
                            v___x_3232_,
                            v___y_3218_,
                            v___y_3219_,
                            v___y_3220_,
                            v___y_3221_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3233_) == 0 {
                            v_a_3234_ = crate::leanh::lean_ctor_get(v___x_3233_, 0);
                            v_isSharedCheck_3241_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3233_)) as u8;
                            if v_isSharedCheck_3241_ == 0 {
                                v___x_3236_ = v___x_3233_;
                                v_isShared_3237_ = v_isSharedCheck_3241_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3234_);
                                crate::leanh::lean_dec(v___x_3233_);
                                v___x_3236_ = crate::leanh::lean_box(0);
                                v_isShared_3237_ = v_isSharedCheck_3241_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_3242_ = crate::leanh::lean_ctor_get(v___x_3233_, 0);
                            v_isSharedCheck_3249_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3233_)) as u8;
                            if v_isSharedCheck_3249_ == 0 {
                                v___x_3244_ = v___x_3233_;
                                v_isShared_3245_ = v_isSharedCheck_3249_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3242_);
                                crate::leanh::lean_dec(v___x_3233_);
                                v___x_3244_ = crate::leanh::lean_box(0);
                                v_isShared_3245_ = v_isSharedCheck_3249_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_3250_ = crate::leanh::lean_ctor_get(v___x_3223_, 0);
                    v_isSharedCheck_3257_ = (!crate::leanh::lean_is_exclusive(v___x_3223_)) as u8;
                    if v_isSharedCheck_3257_ == 0 {
                        v___x_3252_ = v___x_3223_;
                        v_isShared_3253_ = v_isSharedCheck_3257_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3250_);
                        crate::leanh::lean_dec(v___x_3223_);
                        v___x_3252_ = crate::leanh::lean_box(0);
                        v_isShared_3253_ = v_isSharedCheck_3257_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3237_ == 0 {
                    v___x_3239_ = v___x_3236_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3240_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
                    v___x_3239_ = v_reuseFailAlloc_3240_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3239_;
            }
            3 => {
                if v_isShared_3245_ == 0 {
                    v___x_3247_ = v___x_3244_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3248_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
                    v___x_3247_ = v_reuseFailAlloc_3248_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3247_;
            }
            5 => {
                if v_isShared_3253_ == 0 {
                    v___x_3255_ = v___x_3252_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3256_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_a_3250_);
                    v___x_3255_ = v_reuseFailAlloc_3256_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3255_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instReduceEvalMVarId___lam__0___boxed(
    mut v_e_3258_: *mut crate::leanh::LeanObject,
    mut v___y_3259_: *mut crate::leanh::LeanObject,
    mut v___y_3260_: *mut crate::leanh::LeanObject,
    mut v___y_3261_: *mut crate::leanh::LeanObject,
    mut v___y_3262_: *mut crate::leanh::LeanObject,
    mut v___y_3263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3264_ = l_Lean_Meta_instReduceEvalMVarId___lam__0(
        v_e_3258_,
        v___y_3259_,
        v___y_3260_,
        v___y_3261_,
        v___y_3262_,
    );
    crate::leanh::lean_dec(v___y_3262_);
    crate::leanh::lean_dec_ref(v___y_3261_);
    crate::leanh::lean_dec(v___y_3260_);
    crate::leanh::lean_dec_ref(v___y_3259_);
    return v_res_3264_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalLevelMVarId___private__1(
    mut v_e_3272_: *mut crate::leanh::LeanObject,
    mut v_a_3273_: *mut crate::leanh::LeanObject,
    mut v_a_3274_: *mut crate::leanh::LeanObject,
    mut v_a_3275_: *mut crate::leanh::LeanObject,
    mut v_a_3276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: u8 = 0;
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3292_: u8 = 0;
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3296_: u8 = 0;
    let mut v_a_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3300_: u8 = 0;
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3304_: u8 = 0;
    let mut v_a_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3308_: u8 = 0;
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3312_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_3276_);
                crate::leanh::lean_inc_ref(v_a_3275_);
                crate::leanh::lean_inc(v_a_3274_);
                crate::leanh::lean_inc_ref(v_a_3273_);
                v___x_3278_ = lean_whnf(v_e_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
                if crate::leanh::lean_obj_tag(v___x_3278_) == 0 {
                    v_a_3279_ = crate::leanh::lean_ctor_get(v___x_3278_, 0);
                    crate::leanh::lean_inc(v_a_3279_);
                    crate::leanh::lean_dec_ref_known(v___x_3278_, 1);
                    v___x_3280_ = l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1;
                    v___x_3281_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3282_ = l_Lean_Expr_isAppOfArity(v_a_3279_, v___x_3280_, v___x_3281_);
                    if v___x_3282_ == 0 {
                        v___x_3283_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_3279_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
                        return v___x_3283_;
                    } else {
                        v___x_3284_ = l_Lean_Meta_instReduceEvalName___closed__0;
                        v___x_3285_ = l_Lean_Expr_getAppNumArgs(v_a_3279_);
                        v___x_3286_ = lean_nat_sub(v___x_3285_, v___x_3281_);
                        crate::leanh::lean_dec(v___x_3285_);
                        v___x_3287_ = l_Lean_Expr_getRevArg_x21(v_a_3279_, v___x_3286_);
                        crate::leanh::lean_dec(v_a_3279_);
                        v___x_3288_ = l_Lean_Meta_reduceEval___redArg(
                            v___x_3284_,
                            v___x_3287_,
                            v_a_3273_,
                            v_a_3274_,
                            v_a_3275_,
                            v_a_3276_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3288_) == 0 {
                            v_a_3289_ = crate::leanh::lean_ctor_get(v___x_3288_, 0);
                            v_isSharedCheck_3296_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3288_)) as u8;
                            if v_isSharedCheck_3296_ == 0 {
                                v___x_3291_ = v___x_3288_;
                                v_isShared_3292_ = v_isSharedCheck_3296_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3289_);
                                crate::leanh::lean_dec(v___x_3288_);
                                v___x_3291_ = crate::leanh::lean_box(0);
                                v_isShared_3292_ = v_isSharedCheck_3296_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_3297_ = crate::leanh::lean_ctor_get(v___x_3288_, 0);
                            v_isSharedCheck_3304_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3288_)) as u8;
                            if v_isSharedCheck_3304_ == 0 {
                                v___x_3299_ = v___x_3288_;
                                v_isShared_3300_ = v_isSharedCheck_3304_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3297_);
                                crate::leanh::lean_dec(v___x_3288_);
                                v___x_3299_ = crate::leanh::lean_box(0);
                                v_isShared_3300_ = v_isSharedCheck_3304_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_3305_ = crate::leanh::lean_ctor_get(v___x_3278_, 0);
                    v_isSharedCheck_3312_ = (!crate::leanh::lean_is_exclusive(v___x_3278_)) as u8;
                    if v_isSharedCheck_3312_ == 0 {
                        v___x_3307_ = v___x_3278_;
                        v_isShared_3308_ = v_isSharedCheck_3312_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3305_);
                        crate::leanh::lean_dec(v___x_3278_);
                        v___x_3307_ = crate::leanh::lean_box(0);
                        v_isShared_3308_ = v_isSharedCheck_3312_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3292_ == 0 {
                    v___x_3294_ = v___x_3291_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3295_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
                    v___x_3294_ = v_reuseFailAlloc_3295_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3294_;
            }
            3 => {
                if v_isShared_3300_ == 0 {
                    v___x_3302_ = v___x_3299_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3303_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
                    v___x_3302_ = v_reuseFailAlloc_3303_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3302_;
            }
            5 => {
                if v_isShared_3308_ == 0 {
                    v___x_3310_ = v___x_3307_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3311_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
                    v___x_3310_ = v_reuseFailAlloc_3311_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3310_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instReduceEvalLevelMVarId___private__1___boxed(
    mut v_e_3313_: *mut crate::leanh::LeanObject,
    mut v_a_3314_: *mut crate::leanh::LeanObject,
    mut v_a_3315_: *mut crate::leanh::LeanObject,
    mut v_a_3316_: *mut crate::leanh::LeanObject,
    mut v_a_3317_: *mut crate::leanh::LeanObject,
    mut v_a_3318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3319_ = l_Lean_Meta_instReduceEvalLevelMVarId___private__1(
        v_e_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_,
    );
    crate::leanh::lean_dec(v_a_3317_);
    crate::leanh::lean_dec_ref(v_a_3316_);
    crate::leanh::lean_dec(v_a_3315_);
    crate::leanh::lean_dec_ref(v_a_3314_);
    return v_res_3319_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalLevelMVarId___lam__0(
    mut v_e_3320_: *mut crate::leanh::LeanObject,
    mut v___y_3321_: *mut crate::leanh::LeanObject,
    mut v___y_3322_: *mut crate::leanh::LeanObject,
    mut v___y_3323_: *mut crate::leanh::LeanObject,
    mut v___y_3324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: u8 = 0;
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3340_: u8 = 0;
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3344_: u8 = 0;
    let mut v_a_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3348_: u8 = 0;
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3352_: u8 = 0;
    let mut v_a_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3356_: u8 = 0;
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3360_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_3324_);
                crate::leanh::lean_inc_ref(v___y_3323_);
                crate::leanh::lean_inc(v___y_3322_);
                crate::leanh::lean_inc_ref(v___y_3321_);
                v___x_3326_ = lean_whnf(
                    v_e_3320_,
                    v___y_3321_,
                    v___y_3322_,
                    v___y_3323_,
                    v___y_3324_,
                );
                if crate::leanh::lean_obj_tag(v___x_3326_) == 0 {
                    v_a_3327_ = crate::leanh::lean_ctor_get(v___x_3326_, 0);
                    crate::leanh::lean_inc(v_a_3327_);
                    crate::leanh::lean_dec_ref_known(v___x_3326_, 1);
                    v___x_3328_ = l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1;
                    v___x_3329_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3330_ = l_Lean_Expr_isAppOfArity(v_a_3327_, v___x_3328_, v___x_3329_);
                    if v___x_3330_ == 0 {
                        v___x_3331_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_3327_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
                        return v___x_3331_;
                    } else {
                        v___x_3332_ = l_Lean_Meta_instReduceEvalName___closed__0;
                        v___x_3333_ = l_Lean_Expr_getAppNumArgs(v_a_3327_);
                        v___x_3334_ = lean_nat_sub(v___x_3333_, v___x_3329_);
                        crate::leanh::lean_dec(v___x_3333_);
                        v___x_3335_ = l_Lean_Expr_getRevArg_x21(v_a_3327_, v___x_3334_);
                        crate::leanh::lean_dec(v_a_3327_);
                        v___x_3336_ = l_Lean_Meta_reduceEval___redArg(
                            v___x_3332_,
                            v___x_3335_,
                            v___y_3321_,
                            v___y_3322_,
                            v___y_3323_,
                            v___y_3324_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3336_) == 0 {
                            v_a_3337_ = crate::leanh::lean_ctor_get(v___x_3336_, 0);
                            v_isSharedCheck_3344_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3336_)) as u8;
                            if v_isSharedCheck_3344_ == 0 {
                                v___x_3339_ = v___x_3336_;
                                v_isShared_3340_ = v_isSharedCheck_3344_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3337_);
                                crate::leanh::lean_dec(v___x_3336_);
                                v___x_3339_ = crate::leanh::lean_box(0);
                                v_isShared_3340_ = v_isSharedCheck_3344_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_3345_ = crate::leanh::lean_ctor_get(v___x_3336_, 0);
                            v_isSharedCheck_3352_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3336_)) as u8;
                            if v_isSharedCheck_3352_ == 0 {
                                v___x_3347_ = v___x_3336_;
                                v_isShared_3348_ = v_isSharedCheck_3352_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3345_);
                                crate::leanh::lean_dec(v___x_3336_);
                                v___x_3347_ = crate::leanh::lean_box(0);
                                v_isShared_3348_ = v_isSharedCheck_3352_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_3353_ = crate::leanh::lean_ctor_get(v___x_3326_, 0);
                    v_isSharedCheck_3360_ = (!crate::leanh::lean_is_exclusive(v___x_3326_)) as u8;
                    if v_isSharedCheck_3360_ == 0 {
                        v___x_3355_ = v___x_3326_;
                        v_isShared_3356_ = v_isSharedCheck_3360_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3353_);
                        crate::leanh::lean_dec(v___x_3326_);
                        v___x_3355_ = crate::leanh::lean_box(0);
                        v_isShared_3356_ = v_isSharedCheck_3360_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3340_ == 0 {
                    v___x_3342_ = v___x_3339_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3343_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3337_);
                    v___x_3342_ = v_reuseFailAlloc_3343_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3342_;
            }
            3 => {
                if v_isShared_3348_ == 0 {
                    v___x_3350_ = v___x_3347_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3351_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
                    v___x_3350_ = v_reuseFailAlloc_3351_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3350_;
            }
            5 => {
                if v_isShared_3356_ == 0 {
                    v___x_3358_ = v___x_3355_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3359_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
                    v___x_3358_ = v_reuseFailAlloc_3359_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3358_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instReduceEvalLevelMVarId___lam__0___boxed(
    mut v_e_3361_: *mut crate::leanh::LeanObject,
    mut v___y_3362_: *mut crate::leanh::LeanObject,
    mut v___y_3363_: *mut crate::leanh::LeanObject,
    mut v___y_3364_: *mut crate::leanh::LeanObject,
    mut v___y_3365_: *mut crate::leanh::LeanObject,
    mut v___y_3366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3367_ = l_Lean_Meta_instReduceEvalLevelMVarId___lam__0(
        v_e_3361_,
        v___y_3362_,
        v___y_3363_,
        v___y_3364_,
        v___y_3365_,
    );
    crate::leanh::lean_dec(v___y_3365_);
    crate::leanh::lean_dec_ref(v___y_3364_);
    crate::leanh::lean_dec(v___y_3363_);
    crate::leanh::lean_dec_ref(v___y_3362_);
    return v_res_3367_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalFVarId___private__1(
    mut v_e_3375_: *mut crate::leanh::LeanObject,
    mut v_a_3376_: *mut crate::leanh::LeanObject,
    mut v_a_3377_: *mut crate::leanh::LeanObject,
    mut v_a_3378_: *mut crate::leanh::LeanObject,
    mut v_a_3379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: u8 = 0;
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3395_: u8 = 0;
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3399_: u8 = 0;
    let mut v_a_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3403_: u8 = 0;
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3407_: u8 = 0;
    let mut v_a_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3411_: u8 = 0;
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_3379_);
                crate::leanh::lean_inc_ref(v_a_3378_);
                crate::leanh::lean_inc(v_a_3377_);
                crate::leanh::lean_inc_ref(v_a_3376_);
                v___x_3381_ = lean_whnf(v_e_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_);
                if crate::leanh::lean_obj_tag(v___x_3381_) == 0 {
                    v_a_3382_ = crate::leanh::lean_ctor_get(v___x_3381_, 0);
                    crate::leanh::lean_inc(v_a_3382_);
                    crate::leanh::lean_dec_ref_known(v___x_3381_, 1);
                    v___x_3383_ = l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1;
                    v___x_3384_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3385_ = l_Lean_Expr_isAppOfArity(v_a_3382_, v___x_3383_, v___x_3384_);
                    if v___x_3385_ == 0 {
                        v___x_3386_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_3382_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_);
                        return v___x_3386_;
                    } else {
                        v___x_3387_ = l_Lean_Meta_instReduceEvalName___closed__0;
                        v___x_3388_ = l_Lean_Expr_getAppNumArgs(v_a_3382_);
                        v___x_3389_ = lean_nat_sub(v___x_3388_, v___x_3384_);
                        crate::leanh::lean_dec(v___x_3388_);
                        v___x_3390_ = l_Lean_Expr_getRevArg_x21(v_a_3382_, v___x_3389_);
                        crate::leanh::lean_dec(v_a_3382_);
                        v___x_3391_ = l_Lean_Meta_reduceEval___redArg(
                            v___x_3387_,
                            v___x_3390_,
                            v_a_3376_,
                            v_a_3377_,
                            v_a_3378_,
                            v_a_3379_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3391_) == 0 {
                            v_a_3392_ = crate::leanh::lean_ctor_get(v___x_3391_, 0);
                            v_isSharedCheck_3399_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3391_)) as u8;
                            if v_isSharedCheck_3399_ == 0 {
                                v___x_3394_ = v___x_3391_;
                                v_isShared_3395_ = v_isSharedCheck_3399_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3392_);
                                crate::leanh::lean_dec(v___x_3391_);
                                v___x_3394_ = crate::leanh::lean_box(0);
                                v_isShared_3395_ = v_isSharedCheck_3399_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_3400_ = crate::leanh::lean_ctor_get(v___x_3391_, 0);
                            v_isSharedCheck_3407_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3391_)) as u8;
                            if v_isSharedCheck_3407_ == 0 {
                                v___x_3402_ = v___x_3391_;
                                v_isShared_3403_ = v_isSharedCheck_3407_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3400_);
                                crate::leanh::lean_dec(v___x_3391_);
                                v___x_3402_ = crate::leanh::lean_box(0);
                                v_isShared_3403_ = v_isSharedCheck_3407_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_3408_ = crate::leanh::lean_ctor_get(v___x_3381_, 0);
                    v_isSharedCheck_3415_ = (!crate::leanh::lean_is_exclusive(v___x_3381_)) as u8;
                    if v_isSharedCheck_3415_ == 0 {
                        v___x_3410_ = v___x_3381_;
                        v_isShared_3411_ = v_isSharedCheck_3415_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3408_);
                        crate::leanh::lean_dec(v___x_3381_);
                        v___x_3410_ = crate::leanh::lean_box(0);
                        v_isShared_3411_ = v_isSharedCheck_3415_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3395_ == 0 {
                    v___x_3397_ = v___x_3394_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3398_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3392_);
                    v___x_3397_ = v_reuseFailAlloc_3398_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3397_;
            }
            3 => {
                if v_isShared_3403_ == 0 {
                    v___x_3405_ = v___x_3402_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3406_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
                    v___x_3405_ = v_reuseFailAlloc_3406_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3405_;
            }
            5 => {
                if v_isShared_3411_ == 0 {
                    v___x_3413_ = v___x_3410_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3414_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
                    v___x_3413_ = v_reuseFailAlloc_3414_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instReduceEvalFVarId___private__1___boxed(
    mut v_e_3416_: *mut crate::leanh::LeanObject,
    mut v_a_3417_: *mut crate::leanh::LeanObject,
    mut v_a_3418_: *mut crate::leanh::LeanObject,
    mut v_a_3419_: *mut crate::leanh::LeanObject,
    mut v_a_3420_: *mut crate::leanh::LeanObject,
    mut v_a_3421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3422_ = l_Lean_Meta_instReduceEvalFVarId___private__1(
        v_e_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_,
    );
    crate::leanh::lean_dec(v_a_3420_);
    crate::leanh::lean_dec_ref(v_a_3419_);
    crate::leanh::lean_dec(v_a_3418_);
    crate::leanh::lean_dec_ref(v_a_3417_);
    return v_res_3422_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalFVarId___lam__0(
    mut v_e_3423_: *mut crate::leanh::LeanObject,
    mut v___y_3424_: *mut crate::leanh::LeanObject,
    mut v___y_3425_: *mut crate::leanh::LeanObject,
    mut v___y_3426_: *mut crate::leanh::LeanObject,
    mut v___y_3427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: u8 = 0;
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3443_: u8 = 0;
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3447_: u8 = 0;
    let mut v_a_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3451_: u8 = 0;
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut v_a_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3459_: u8 = 0;
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_3427_);
                crate::leanh::lean_inc_ref(v___y_3426_);
                crate::leanh::lean_inc(v___y_3425_);
                crate::leanh::lean_inc_ref(v___y_3424_);
                v___x_3429_ = lean_whnf(
                    v_e_3423_,
                    v___y_3424_,
                    v___y_3425_,
                    v___y_3426_,
                    v___y_3427_,
                );
                if crate::leanh::lean_obj_tag(v___x_3429_) == 0 {
                    v_a_3430_ = crate::leanh::lean_ctor_get(v___x_3429_, 0);
                    crate::leanh::lean_inc(v_a_3430_);
                    crate::leanh::lean_dec_ref_known(v___x_3429_, 1);
                    v___x_3431_ = l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1;
                    v___x_3432_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3433_ = l_Lean_Expr_isAppOfArity(v_a_3430_, v___x_3431_, v___x_3432_);
                    if v___x_3433_ == 0 {
                        v___x_3434_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_3430_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
                        return v___x_3434_;
                    } else {
                        v___x_3435_ = l_Lean_Meta_instReduceEvalName___closed__0;
                        v___x_3436_ = l_Lean_Expr_getAppNumArgs(v_a_3430_);
                        v___x_3437_ = lean_nat_sub(v___x_3436_, v___x_3432_);
                        crate::leanh::lean_dec(v___x_3436_);
                        v___x_3438_ = l_Lean_Expr_getRevArg_x21(v_a_3430_, v___x_3437_);
                        crate::leanh::lean_dec(v_a_3430_);
                        v___x_3439_ = l_Lean_Meta_reduceEval___redArg(
                            v___x_3435_,
                            v___x_3438_,
                            v___y_3424_,
                            v___y_3425_,
                            v___y_3426_,
                            v___y_3427_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3439_) == 0 {
                            v_a_3440_ = crate::leanh::lean_ctor_get(v___x_3439_, 0);
                            v_isSharedCheck_3447_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3439_)) as u8;
                            if v_isSharedCheck_3447_ == 0 {
                                v___x_3442_ = v___x_3439_;
                                v_isShared_3443_ = v_isSharedCheck_3447_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3440_);
                                crate::leanh::lean_dec(v___x_3439_);
                                v___x_3442_ = crate::leanh::lean_box(0);
                                v_isShared_3443_ = v_isSharedCheck_3447_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_3448_ = crate::leanh::lean_ctor_get(v___x_3439_, 0);
                            v_isSharedCheck_3455_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3439_)) as u8;
                            if v_isSharedCheck_3455_ == 0 {
                                v___x_3450_ = v___x_3439_;
                                v_isShared_3451_ = v_isSharedCheck_3455_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3448_);
                                crate::leanh::lean_dec(v___x_3439_);
                                v___x_3450_ = crate::leanh::lean_box(0);
                                v_isShared_3451_ = v_isSharedCheck_3455_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_3456_ = crate::leanh::lean_ctor_get(v___x_3429_, 0);
                    v_isSharedCheck_3463_ = (!crate::leanh::lean_is_exclusive(v___x_3429_)) as u8;
                    if v_isSharedCheck_3463_ == 0 {
                        v___x_3458_ = v___x_3429_;
                        v_isShared_3459_ = v_isSharedCheck_3463_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3456_);
                        crate::leanh::lean_dec(v___x_3429_);
                        v___x_3458_ = crate::leanh::lean_box(0);
                        v_isShared_3459_ = v_isSharedCheck_3463_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3443_ == 0 {
                    v___x_3445_ = v___x_3442_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3446_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3440_);
                    v___x_3445_ = v_reuseFailAlloc_3446_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3445_;
            }
            3 => {
                if v_isShared_3451_ == 0 {
                    v___x_3453_ = v___x_3450_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3454_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
                    v___x_3453_ = v_reuseFailAlloc_3454_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3453_;
            }
            5 => {
                if v_isShared_3459_ == 0 {
                    v___x_3461_ = v___x_3458_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3462_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
                    v___x_3461_ = v_reuseFailAlloc_3462_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3461_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instReduceEvalFVarId___lam__0___boxed(
    mut v_e_3464_: *mut crate::leanh::LeanObject,
    mut v___y_3465_: *mut crate::leanh::LeanObject,
    mut v___y_3466_: *mut crate::leanh::LeanObject,
    mut v___y_3467_: *mut crate::leanh::LeanObject,
    mut v___y_3468_: *mut crate::leanh::LeanObject,
    mut v___y_3469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3470_ = l_Lean_Meta_instReduceEvalFVarId___lam__0(
        v_e_3464_,
        v___y_3465_,
        v___y_3466_,
        v___y_3467_,
        v___y_3468_,
    );
    crate::leanh::lean_dec(v___y_3468_);
    crate::leanh::lean_dec_ref(v___y_3467_);
    crate::leanh::lean_dec(v___y_3466_);
    crate::leanh::lean_dec_ref(v___y_3465_);
    return v_res_3470_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_ReduceEval(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Offset(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_ReduceEval(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_ReduceEval(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Offset(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ReduceEval(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_ReduceEval(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_ReduceEval(builtin);
}
