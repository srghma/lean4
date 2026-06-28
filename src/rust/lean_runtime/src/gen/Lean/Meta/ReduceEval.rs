// Lean compiler output
// Module: Lean.Meta.ReduceEval
// Imports: Lean.Meta.Offset
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_num___override, l_Lean_Name_str___override,
};
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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_6, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__0_value: LeanStringObject<40> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [114, 101, 100, 117, 99, 101, 69, 118, 97, 108, 58, 32, 102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 101, 118, 97, 108, 117, 97, 116, 101, 32, 97, 114, 103, 117, 109, 101, 110, 116, 0]};
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_instReduceEvalNat___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReduceEvalNat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReduceEvalNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalNat___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_instReduceEvalNat: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalNat___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__0_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__1_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__0_value
        ) as *mut LeanObject,
        18184376426117065311 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__1_value
        ) as *mut LeanObject,
        4893146552088433753 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__3_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__3_value)
        as *mut LeanObject;
static l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__0_value
        ) as *mut LeanObject,
        18184376426117065311 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__3_value
        ) as *mut LeanObject,
        9480010471355609749 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReduceEvalString___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReduceEvalString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalString___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_instReduceEvalString: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalString___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2_value)
        as *mut LeanObject;
static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1_value
        ) as *mut LeanObject,
        13306843946249674491 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2_value
        ) as *mut LeanObject,
        7229350633979142691 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4_value)
        as *mut LeanObject;
static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1_value
        ) as *mut LeanObject,
        13306843946249674491 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4_value
        ) as *mut LeanObject,
        8392322758047580095 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__6_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__6_value)
        as *mut LeanObject;
static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1_value
        ) as *mut LeanObject,
        13306843946249674491 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__6_value
        ) as *mut LeanObject,
        8742792063936078747 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalName___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReduceEvalName___private__1___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReduceEvalName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalName___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_instReduceEvalName: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalName___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__1_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__2_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__0_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__1_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__1_value
) as *mut LeanObject;
static l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__0_value
        ) as *mut LeanObject,
        15815496672699636542 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__1_value
        ) as *mut LeanObject,
        5825593324384481310 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalBitVec___private__1___closed__0_value: LeanStringObject<7> =
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
        m_data: [66, 105, 116, 86, 101, 99, 0],
    };
static mut l_Lean_Meta_instReduceEvalBitVec___private__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBitVec___private__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalBitVec___private__1___closed__1_value: LeanStringObject<6> =
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
        m_data: [111, 102, 70, 105, 110, 0],
    };
static mut l_Lean_Meta_instReduceEvalBitVec___private__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBitVec___private__1___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_instReduceEvalBitVec___private__1___closed__2_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBitVec___private__1___closed__0_value)
                as *mut LeanObject,
            5394957827732845164 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_instReduceEvalBitVec___private__1___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_instReduceEvalBitVec___private__1___closed__2_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBitVec___private__1___closed__1_value)
                as *mut LeanObject,
            3686919969481140037 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReduceEvalBitVec___private__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBitVec___private__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalBool___private__1___closed__0_value: LeanStringObject<5> =
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
        m_data: [66, 111, 111, 108, 0],
    };
static mut l_Lean_Meta_instReduceEvalBool___private__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___private__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalBool___private__1___closed__1_value: LeanStringObject<5> =
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
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lean_Meta_instReduceEvalBool___private__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___private__1___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_instReduceEvalBool___private__1___closed__2_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___private__1___closed__0_value)
                as *mut LeanObject,
            12882480457794858234 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_instReduceEvalBool___private__1___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___private__1___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___private__1___closed__1_value)
                as *mut LeanObject,
            9255189395584251158 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReduceEvalBool___private__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___private__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalBool___private__1___closed__3_value: LeanStringObject<6> =
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
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Meta_instReduceEvalBool___private__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___private__1___closed__3_value)
        as *mut LeanObject;
static l_Lean_Meta_instReduceEvalBool___private__1___closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___private__1___closed__0_value)
                as *mut LeanObject,
            12882480457794858234 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_instReduceEvalBool___private__1___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___private__1___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___private__1___closed__3_value)
                as *mut LeanObject,
            15761733860085307253 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReduceEvalBool___private__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___private__1___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalBool___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReduceEvalBool___private__1___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReduceEvalBool___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_instReduceEvalBool: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBool___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__0_value: LeanStringObject<
    11,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__1_value: LeanStringObject<
    8,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__2_value: LeanStringObject<
    9,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__3_value: LeanStringObject<
    15,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__4_value: LeanStringObject<
    13,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalBinderInfo___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReduceEvalBinderInfo___private__1___boxed
            as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReduceEvalBinderInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBinderInfo___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_instReduceEvalBinderInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalBinderInfo___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalLiteral___private__1___closed__0_value: LeanStringObject<8> =
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
        m_data: [76, 105, 116, 101, 114, 97, 108, 0],
    };
static mut l_Lean_Meta_instReduceEvalLiteral___private__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalLiteral___private__1___closed__1_value: LeanStringObject<7> =
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
        m_data: [110, 97, 116, 86, 97, 108, 0],
    };
static mut l_Lean_Meta_instReduceEvalLiteral___private__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(
                l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value
            ) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__0_value)
                as *mut LeanObject,
            7001815944269665831 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__1_value)
                as *mut LeanObject,
            9295767770006931264 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalLiteral___private__1___closed__3_value: LeanStringObject<7> =
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
        m_data: [115, 116, 114, 86, 97, 108, 0],
    };
static mut l_Lean_Meta_instReduceEvalLiteral___private__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__3_value)
        as *mut LeanObject;
static l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(
                l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value
            ) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__0_value)
                as *mut LeanObject,
            7001815944269665831 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__3_value)
                as *mut LeanObject,
            2005404019190257220 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___private__1___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalLiteral___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReduceEvalLiteral___private__1___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReduceEvalLiteral___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_instReduceEvalLiteral: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLiteral___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalMVarId___private__1___closed__0_value: LeanStringObject<7> =
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
        m_data: [77, 86, 97, 114, 73, 100, 0],
    };
static mut l_Lean_Meta_instReduceEvalMVarId___private__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalMVarId___private__1___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(
                l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value
            ) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instReduceEvalMVarId___private__1___closed__0_value)
                as *mut LeanObject,
            5356933541775719089 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__1_value
            ) as *mut LeanObject,
            10225135193421524061 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalMVarId___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReduceEvalMVarId___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReduceEvalMVarId___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalMVarId___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_instReduceEvalMVarId: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalMVarId___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__0_value: LeanStringObject<
    12,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__0_value)
            as *mut LeanObject,
        10629041231479782489 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__1_value
            ) as *mut LeanObject,
            16867186451750755797 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalLevelMVarId___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReduceEvalLevelMVarId___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReduceEvalLevelMVarId___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLevelMVarId___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_instReduceEvalLevelMVarId: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalLevelMVarId___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalFVarId___private__1___closed__0_value: LeanStringObject<7> =
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
        m_data: [70, 86, 97, 114, 73, 100, 0],
    };
static mut l_Lean_Meta_instReduceEvalFVarId___private__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalFVarId___private__1___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(
                l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0_value
            ) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instReduceEvalFVarId___private__1___closed__0_value)
                as *mut LeanObject,
            6212595679582900358 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__1_value
            ) as *mut LeanObject,
            6968149084986791158 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReduceEvalFVarId___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReduceEvalFVarId___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReduceEvalFVarId___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalFVarId___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_instReduceEvalFVarId: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReduceEvalFVarId___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_reduceEval___redArg(
    mut v_inst_1737_: *mut LeanObject,
    mut v_e_1738_: *mut LeanObject,
    mut v_a_1739_: *mut LeanObject,
    mut v_a_1740_: *mut LeanObject,
    mut v_a_1741_: *mut LeanObject,
    mut v_a_1742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1745_: u8 = 0;
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1767_: u8 = 0;
    let mut v_trackZetaDelta_1768_: u8 = 0;
    let mut v_zetaDeltaSet_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_1775_: u8 = 0;
    let mut v_inTypeClassResolution_1776_: u8 = 0;
    let mut v_cacheInferType_1777_: u8 = 0;
    let mut v_config_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: u64 = 0;
    let mut v___x_1781_: u64 = 0;
    let mut v___x_1782_: u64 = 0;
    let mut v___x_1783_: u64 = 0;
    let mut v___x_1784_: u64 = 0;
    let mut v_key_1785_: u64 = 0;
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1790_: u8 = 0;
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transparency_1792_: u8 = 0;
    let mut v___x_1793_: u8 = 0;
    let mut v___x_1794_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1791_ = l_Lean_Meta_Context_config(v_a_1739_);
                v_transparency_1792_ = lean_ctor_get_uint8(v___x_1791_, 9 as u32);
                lean_dec_ref(v___x_1791_);
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
                v_foApprox_1747_ = lean_ctor_get_uint8(v___x_1746_, 0 as u32);
                v_ctxApprox_1748_ = lean_ctor_get_uint8(v___x_1746_, 1 as u32);
                v_quasiPatternApprox_1749_ = lean_ctor_get_uint8(v___x_1746_, 2 as u32);
                v_constApprox_1750_ = lean_ctor_get_uint8(v___x_1746_, 3 as u32);
                v_isDefEqStuckEx_1751_ = lean_ctor_get_uint8(v___x_1746_, 4 as u32);
                v_unificationHints_1752_ = lean_ctor_get_uint8(v___x_1746_, 5 as u32);
                v_proofIrrelevance_1753_ = lean_ctor_get_uint8(v___x_1746_, 6 as u32);
                v_assignSyntheticOpaque_1754_ = lean_ctor_get_uint8(v___x_1746_, 7 as u32);
                v_offsetCnstrs_1755_ = lean_ctor_get_uint8(v___x_1746_, 8 as u32);
                v_etaStruct_1756_ = lean_ctor_get_uint8(v___x_1746_, 10 as u32);
                v_univApprox_1757_ = lean_ctor_get_uint8(v___x_1746_, 11 as u32);
                v_iota_1758_ = lean_ctor_get_uint8(v___x_1746_, 12 as u32);
                v_beta_1759_ = lean_ctor_get_uint8(v___x_1746_, 13 as u32);
                v_proj_1760_ = lean_ctor_get_uint8(v___x_1746_, 14 as u32);
                v_zeta_1761_ = lean_ctor_get_uint8(v___x_1746_, 15 as u32);
                v_zetaDelta_1762_ = lean_ctor_get_uint8(v___x_1746_, 16 as u32);
                v_zetaUnused_1763_ = lean_ctor_get_uint8(v___x_1746_, 17 as u32);
                v_zetaHave_1764_ = lean_ctor_get_uint8(v___x_1746_, 18 as u32);
                v_isSharedCheck_1790_ = (!lean_is_exclusive(v___x_1746_)) as u8;
                if v_isSharedCheck_1790_ == 0 {
                    v___x_1766_ = v___x_1746_;
                    v_isShared_1767_ = v_isSharedCheck_1790_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_1746_);
                    v___x_1766_ = lean_box(0);
                    v_isShared_1767_ = v_isSharedCheck_1790_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_trackZetaDelta_1768_ = lean_ctor_get_uint8(
                    v_a_1739_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_1769_ = lean_ctor_get(v_a_1739_, 1);
                v_lctx_1770_ = lean_ctor_get(v_a_1739_, 2);
                v_localInstances_1771_ = lean_ctor_get(v_a_1739_, 3);
                v_defEqCtx_x3f_1772_ = lean_ctor_get(v_a_1739_, 4);
                v_synthPendingDepth_1773_ = lean_ctor_get(v_a_1739_, 5);
                v_canUnfold_x3f_1774_ = lean_ctor_get(v_a_1739_, 6);
                v_univApprox_1775_ = lean_ctor_get_uint8(
                    v_a_1739_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_1776_ = lean_ctor_get_uint8(
                    v_a_1739_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_1777_ = lean_ctor_get_uint8(
                    v_a_1739_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_1767_ == 0 {
                    v_config_1779_ = v___x_1766_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1789_, 0 as u32, v_foApprox_1747_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1789_, 1 as u32, v_ctxApprox_1748_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1789_,
                        2 as u32,
                        v_quasiPatternApprox_1749_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_1789_, 3 as u32, v_constApprox_1750_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1789_, 4 as u32, v_isDefEqStuckEx_1751_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1789_, 5 as u32, v_unificationHints_1752_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1789_, 6 as u32, v_proofIrrelevance_1753_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1789_,
                        7 as u32,
                        v_assignSyntheticOpaque_1754_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_1789_, 8 as u32, v_offsetCnstrs_1755_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1789_, 10 as u32, v_etaStruct_1756_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1789_, 11 as u32, v_univApprox_1757_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1789_, 12 as u32, v_iota_1758_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1789_, 13 as u32, v_beta_1759_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1789_, 14 as u32, v_proj_1760_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1789_, 15 as u32, v_zeta_1761_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1789_, 16 as u32, v_zetaDelta_1762_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1789_, 17 as u32, v_zetaUnused_1763_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_1789_, 18 as u32, v_zetaHave_1764_);
                    v_config_1779_ = v_reuseFailAlloc_1789_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(v_config_1779_, 9 as u32, v___y_1745_);
                v___x_1780_ = l_Lean_Meta_Context_configKey(v_a_1739_);
                v___x_1781_ = 3u64;
                v___x_1782_ = lean_uint64_shift_right(v___x_1780_, v___x_1781_);
                v___x_1783_ = lean_uint64_shift_left(v___x_1782_, v___x_1781_);
                v___x_1784_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_1745_);
                v_key_1785_ = lean_uint64_lor(v___x_1783_, v___x_1784_);
                v___x_1786_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_1786_, 0, v_config_1779_);
                lean_ctor_set_uint64(
                    v___x_1786_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_1785_,
                );
                lean_inc(v_canUnfold_x3f_1774_);
                lean_inc(v_synthPendingDepth_1773_);
                lean_inc(v_defEqCtx_x3f_1772_);
                lean_inc_ref(v_localInstances_1771_);
                lean_inc_ref(v_lctx_1770_);
                lean_inc(v_zetaDeltaSet_1769_);
                v___x_1787_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_1787_, 0, v___x_1786_);
                lean_ctor_set(v___x_1787_, 1, v_zetaDeltaSet_1769_);
                lean_ctor_set(v___x_1787_, 2, v_lctx_1770_);
                lean_ctor_set(v___x_1787_, 3, v_localInstances_1771_);
                lean_ctor_set(v___x_1787_, 4, v_defEqCtx_x3f_1772_);
                lean_ctor_set(v___x_1787_, 5, v_synthPendingDepth_1773_);
                lean_ctor_set(v___x_1787_, 6, v_canUnfold_x3f_1774_);
                lean_ctor_set_uint8(
                    v___x_1787_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_1768_,
                );
                lean_ctor_set_uint8(
                    v___x_1787_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_1775_,
                );
                lean_ctor_set_uint8(
                    v___x_1787_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_1776_,
                );
                lean_ctor_set_uint8(
                    v___x_1787_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_1777_,
                );
                lean_inc(v_a_1742_);
                lean_inc_ref(v_a_1741_);
                lean_inc(v_a_1740_);
                v___x_1788_ = lean_apply_6(
                    v_inst_1737_,
                    v_e_1738_,
                    v___x_1787_,
                    v_a_1740_,
                    v_a_1741_,
                    v_a_1742_,
                    lean_box(0),
                );
                return v___x_1788_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_reduceEval___redArg___boxed(
    mut v_inst_1795_: *mut LeanObject,
    mut v_e_1796_: *mut LeanObject,
    mut v_a_1797_: *mut LeanObject,
    mut v_a_1798_: *mut LeanObject,
    mut v_a_1799_: *mut LeanObject,
    mut v_a_1800_: *mut LeanObject,
    mut v_a_1801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1802_: *mut LeanObject = core::ptr::null_mut();
    v_res_1802_ = l_Lean_Meta_reduceEval___redArg(
        v_inst_1795_,
        v_e_1796_,
        v_a_1797_,
        v_a_1798_,
        v_a_1799_,
        v_a_1800_,
    );
    lean_dec(v_a_1800_);
    lean_dec_ref(v_a_1799_);
    lean_dec(v_a_1798_);
    lean_dec_ref(v_a_1797_);
    return v_res_1802_;
}
pub unsafe fn l_Lean_Meta_reduceEval(
    mut v_00_u03b1_1803_: *mut LeanObject,
    mut v_inst_1804_: *mut LeanObject,
    mut v_e_1805_: *mut LeanObject,
    mut v_a_1806_: *mut LeanObject,
    mut v_a_1807_: *mut LeanObject,
    mut v_a_1808_: *mut LeanObject,
    mut v_a_1809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1812_: *mut LeanObject,
    mut v_inst_1813_: *mut LeanObject,
    mut v_e_1814_: *mut LeanObject,
    mut v_a_1815_: *mut LeanObject,
    mut v_a_1816_: *mut LeanObject,
    mut v_a_1817_: *mut LeanObject,
    mut v_a_1818_: *mut LeanObject,
    mut v_a_1819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1820_: *mut LeanObject = core::ptr::null_mut();
    v_res_1820_ = l_Lean_Meta_reduceEval(
        v_00_u03b1_1812_,
        v_inst_1813_,
        v_e_1814_,
        v_a_1815_,
        v_a_1816_,
        v_a_1817_,
        v_a_1818_,
    );
    lean_dec(v_a_1818_);
    lean_dec_ref(v_a_1817_);
    lean_dec(v_a_1816_);
    lean_dec_ref(v_a_1815_);
    return v_res_1820_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(
    mut v_msgData_1821_: *mut LeanObject,
    mut v___y_1822_: *mut LeanObject,
    mut v___y_1823_: *mut LeanObject,
    mut v___y_1824_: *mut LeanObject,
    mut v___y_1825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    v___x_1827_ = lean_st_ref_get(v___y_1825_);
    v_env_1828_ = lean_ctor_get(v___x_1827_, 0);
    lean_inc_ref(v_env_1828_);
    lean_dec(v___x_1827_);
    v___x_1829_ = lean_st_ref_get(v___y_1823_);
    v_mctx_1830_ = lean_ctor_get(v___x_1829_, 0);
    lean_inc_ref(v_mctx_1830_);
    lean_dec(v___x_1829_);
    v_lctx_1831_ = lean_ctor_get(v___y_1822_, 2);
    v_options_1832_ = lean_ctor_get(v___y_1824_, 2);
    lean_inc_ref(v_options_1832_);
    lean_inc_ref(v_lctx_1831_);
    v___x_1833_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1833_, 0, v_env_1828_);
    lean_ctor_set(v___x_1833_, 1, v_mctx_1830_);
    lean_ctor_set(v___x_1833_, 2, v_lctx_1831_);
    lean_ctor_set(v___x_1833_, 3, v_options_1832_);
    v___x_1834_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1834_, 0, v___x_1833_);
    lean_ctor_set(v___x_1834_, 1, v_msgData_1821_);
    v___x_1835_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1835_, 0, v___x_1834_);
    return v___x_1835_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0___boxed(
    mut v_msgData_1836_: *mut LeanObject,
    mut v___y_1837_: *mut LeanObject,
    mut v___y_1838_: *mut LeanObject,
    mut v___y_1839_: *mut LeanObject,
    mut v___y_1840_: *mut LeanObject,
    mut v___y_1841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1842_: *mut LeanObject = core::ptr::null_mut();
    v_res_1842_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(v_msgData_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
    lean_dec(v___y_1840_);
    lean_dec_ref(v___y_1839_);
    lean_dec(v___y_1838_);
    lean_dec_ref(v___y_1837_);
    return v_res_1842_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(
    mut v_msg_1843_: *mut LeanObject,
    mut v___y_1844_: *mut LeanObject,
    mut v___y_1845_: *mut LeanObject,
    mut v___y_1846_: *mut LeanObject,
    mut v___y_1847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1854_: u8 = 0;
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1859_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1849_ = lean_ctor_get(v___y_1846_, 5);
                v___x_1850_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0_spec__0(v_msg_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
                v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
                v_isSharedCheck_1859_ = (!lean_is_exclusive(v___x_1850_)) as u8;
                if v_isSharedCheck_1859_ == 0 {
                    v___x_1853_ = v___x_1850_;
                    v_isShared_1854_ = v_isSharedCheck_1859_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1851_);
                    lean_dec(v___x_1850_);
                    v___x_1853_ = lean_box(0);
                    v_isShared_1854_ = v_isSharedCheck_1859_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1849_);
                v___x_1855_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1855_, 0, v_ref_1849_);
                lean_ctor_set(v___x_1855_, 1, v_a_1851_);
                if v_isShared_1854_ == 0 {
                    lean_ctor_set_tag(v___x_1853_, 1);
                    lean_ctor_set(v___x_1853_, 0, v___x_1855_);
                    v___x_1857_ = v___x_1853_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
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
    mut v_msg_1860_: *mut LeanObject,
    mut v___y_1861_: *mut LeanObject,
    mut v___y_1862_: *mut LeanObject,
    mut v___y_1863_: *mut LeanObject,
    mut v___y_1864_: *mut LeanObject,
    mut v___y_1865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1866_: *mut LeanObject = core::ptr::null_mut();
    v_res_1866_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(v_msg_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
    lean_dec(v___y_1864_);
    lean_dec_ref(v___y_1863_);
    lean_dec(v___y_1862_);
    lean_dec_ref(v___y_1861_);
    return v_res_1866_;
}
pub unsafe fn _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    v___x_1868_ =
        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__0;
    v___x_1869_ = l_Lean_stringToMessageData(v___x_1868_);
    return v___x_1869_;
}
pub unsafe fn l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
    mut v_e_1870_: *mut LeanObject,
    mut v_a_1871_: *mut LeanObject,
    mut v_a_1872_: *mut LeanObject,
    mut v_a_1873_: *mut LeanObject,
    mut v_a_1874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    v___x_1876_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1_once), _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___closed__1);
    v___x_1877_ = l_Lean_indentExpr(v_e_1870_);
    v___x_1878_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1878_, 0, v___x_1876_);
    lean_ctor_set(v___x_1878_, 1, v___x_1877_);
    v___x_1879_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(v___x_1878_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
    return v___x_1879_;
}
pub unsafe fn l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___boxed(
    mut v_e_1880_: *mut LeanObject,
    mut v_a_1881_: *mut LeanObject,
    mut v_a_1882_: *mut LeanObject,
    mut v_a_1883_: *mut LeanObject,
    mut v_a_1884_: *mut LeanObject,
    mut v_a_1885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1886_: *mut LeanObject = core::ptr::null_mut();
    v_res_1886_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
        v_e_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_,
    );
    lean_dec(v_a_1884_);
    lean_dec_ref(v_a_1883_);
    lean_dec(v_a_1882_);
    lean_dec_ref(v_a_1881_);
    return v_res_1886_;
}
pub unsafe fn l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(
    mut v_00_u03b1_1887_: *mut LeanObject,
    mut v_e_1888_: *mut LeanObject,
    mut v_a_1889_: *mut LeanObject,
    mut v_a_1890_: *mut LeanObject,
    mut v_a_1891_: *mut LeanObject,
    mut v_a_1892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    v___x_1894_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
        v_e_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_,
    );
    return v___x_1894_;
}
pub unsafe fn l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___boxed(
    mut v_00_u03b1_1895_: *mut LeanObject,
    mut v_e_1896_: *mut LeanObject,
    mut v_a_1897_: *mut LeanObject,
    mut v_a_1898_: *mut LeanObject,
    mut v_a_1899_: *mut LeanObject,
    mut v_a_1900_: *mut LeanObject,
    mut v_a_1901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1902_: *mut LeanObject = core::ptr::null_mut();
    v_res_1902_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(
        v_00_u03b1_1895_,
        v_e_1896_,
        v_a_1897_,
        v_a_1898_,
        v_a_1899_,
        v_a_1900_,
    );
    lean_dec(v_a_1900_);
    lean_dec_ref(v_a_1899_);
    lean_dec(v_a_1898_);
    lean_dec_ref(v_a_1897_);
    return v_res_1902_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0(
    mut v_00_u03b1_1903_: *mut LeanObject,
    mut v_msg_1904_: *mut LeanObject,
    mut v___y_1905_: *mut LeanObject,
    mut v___y_1906_: *mut LeanObject,
    mut v___y_1907_: *mut LeanObject,
    mut v___y_1908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    v___x_1910_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___redArg(v_msg_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
    return v___x_1910_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0___boxed(
    mut v_00_u03b1_1911_: *mut LeanObject,
    mut v_msg_1912_: *mut LeanObject,
    mut v___y_1913_: *mut LeanObject,
    mut v___y_1914_: *mut LeanObject,
    mut v___y_1915_: *mut LeanObject,
    mut v___y_1916_: *mut LeanObject,
    mut v___y_1917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1918_: *mut LeanObject = core::ptr::null_mut();
    v_res_1918_ = l_Lean_throwError___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval_spec__0(v_00_u03b1_1911_, v_msg_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
    lean_dec(v___y_1916_);
    lean_dec_ref(v___y_1915_);
    lean_dec(v___y_1914_);
    lean_dec_ref(v___y_1913_);
    return v_res_1918_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalNat___private__1(
    mut v_e_1919_: *mut LeanObject,
    mut v_a_1920_: *mut LeanObject,
    mut v_a_1921_: *mut LeanObject,
    mut v_a_1922_: *mut LeanObject,
    mut v_a_1923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1931_: u8 = 0;
    let mut v_val_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1937_: u8 = 0;
    let mut v_a_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1941_: u8 = 0;
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1945_: u8 = 0;
    let mut v_a_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1949_: u8 = 0;
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1953_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_1923_);
                lean_inc_ref(v_a_1922_);
                lean_inc(v_a_1921_);
                lean_inc_ref(v_a_1920_);
                v___x_1925_ = lean_whnf(v_e_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
                if lean_obj_tag(v___x_1925_) == 0 {
                    v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
                    lean_inc_n(v_a_1926_, 2);
                    lean_dec_ref_known(v___x_1925_, 1);
                    v___x_1927_ =
                        l_Lean_Meta_evalNat(v_a_1926_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
                    if lean_obj_tag(v___x_1927_) == 0 {
                        v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
                        v_isSharedCheck_1937_ = (!lean_is_exclusive(v___x_1927_)) as u8;
                        if v_isSharedCheck_1937_ == 0 {
                            v___x_1930_ = v___x_1927_;
                            v_isShared_1931_ = v_isSharedCheck_1937_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1928_);
                            lean_dec(v___x_1927_);
                            v___x_1930_ = lean_box(0);
                            v_isShared_1931_ = v_isSharedCheck_1937_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1926_);
                        v_a_1938_ = lean_ctor_get(v___x_1927_, 0);
                        v_isSharedCheck_1945_ = (!lean_is_exclusive(v___x_1927_)) as u8;
                        if v_isSharedCheck_1945_ == 0 {
                            v___x_1940_ = v___x_1927_;
                            v_isShared_1941_ = v_isSharedCheck_1945_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1938_);
                            lean_dec(v___x_1927_);
                            v___x_1940_ = lean_box(0);
                            v_isShared_1941_ = v_isSharedCheck_1945_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_1946_ = lean_ctor_get(v___x_1925_, 0);
                    v_isSharedCheck_1953_ = (!lean_is_exclusive(v___x_1925_)) as u8;
                    if v_isSharedCheck_1953_ == 0 {
                        v___x_1948_ = v___x_1925_;
                        v_isShared_1949_ = v_isSharedCheck_1953_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1946_);
                        lean_dec(v___x_1925_);
                        v___x_1948_ = lean_box(0);
                        v_isShared_1949_ = v_isSharedCheck_1953_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1928_) == 1 {
                    lean_dec(v_a_1926_);
                    v_val_1932_ = lean_ctor_get(v_a_1928_, 0);
                    lean_inc(v_val_1932_);
                    lean_dec_ref_known(v_a_1928_, 1);
                    if v_isShared_1931_ == 0 {
                        lean_ctor_set(v___x_1930_, 0, v_val_1932_);
                        v___x_1934_ = v___x_1930_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_val_1932_);
                        v___x_1934_ = v_reuseFailAlloc_1935_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1930_);
                    lean_dec(v_a_1928_);
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
                    v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
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
                    v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
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
    mut v_e_1954_: *mut LeanObject,
    mut v_a_1955_: *mut LeanObject,
    mut v_a_1956_: *mut LeanObject,
    mut v_a_1957_: *mut LeanObject,
    mut v_a_1958_: *mut LeanObject,
    mut v_a_1959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1960_: *mut LeanObject = core::ptr::null_mut();
    v_res_1960_ = l_Lean_Meta_instReduceEvalNat___private__1(
        v_e_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_,
    );
    lean_dec(v_a_1958_);
    lean_dec_ref(v_a_1957_);
    lean_dec(v_a_1956_);
    lean_dec_ref(v_a_1955_);
    return v_res_1960_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalNat___lam__0(
    mut v_e_1961_: *mut LeanObject,
    mut v___y_1962_: *mut LeanObject,
    mut v___y_1963_: *mut LeanObject,
    mut v___y_1964_: *mut LeanObject,
    mut v___y_1965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1973_: u8 = 0;
    let mut v_val_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1979_: u8 = 0;
    let mut v_a_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1983_: u8 = 0;
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1987_: u8 = 0;
    let mut v_a_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1991_: u8 = 0;
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1995_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1965_);
                lean_inc_ref(v___y_1964_);
                lean_inc(v___y_1963_);
                lean_inc_ref(v___y_1962_);
                v___x_1967_ = lean_whnf(
                    v_e_1961_,
                    v___y_1962_,
                    v___y_1963_,
                    v___y_1964_,
                    v___y_1965_,
                );
                if lean_obj_tag(v___x_1967_) == 0 {
                    v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
                    lean_inc_n(v_a_1968_, 2);
                    lean_dec_ref_known(v___x_1967_, 1);
                    v___x_1969_ = l_Lean_Meta_evalNat(
                        v_a_1968_,
                        v___y_1962_,
                        v___y_1963_,
                        v___y_1964_,
                        v___y_1965_,
                    );
                    if lean_obj_tag(v___x_1969_) == 0 {
                        v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
                        v_isSharedCheck_1979_ = (!lean_is_exclusive(v___x_1969_)) as u8;
                        if v_isSharedCheck_1979_ == 0 {
                            v___x_1972_ = v___x_1969_;
                            v_isShared_1973_ = v_isSharedCheck_1979_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1970_);
                            lean_dec(v___x_1969_);
                            v___x_1972_ = lean_box(0);
                            v_isShared_1973_ = v_isSharedCheck_1979_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1968_);
                        v_a_1980_ = lean_ctor_get(v___x_1969_, 0);
                        v_isSharedCheck_1987_ = (!lean_is_exclusive(v___x_1969_)) as u8;
                        if v_isSharedCheck_1987_ == 0 {
                            v___x_1982_ = v___x_1969_;
                            v_isShared_1983_ = v_isSharedCheck_1987_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1980_);
                            lean_dec(v___x_1969_);
                            v___x_1982_ = lean_box(0);
                            v_isShared_1983_ = v_isSharedCheck_1987_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_1988_ = lean_ctor_get(v___x_1967_, 0);
                    v_isSharedCheck_1995_ = (!lean_is_exclusive(v___x_1967_)) as u8;
                    if v_isSharedCheck_1995_ == 0 {
                        v___x_1990_ = v___x_1967_;
                        v_isShared_1991_ = v_isSharedCheck_1995_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1988_);
                        lean_dec(v___x_1967_);
                        v___x_1990_ = lean_box(0);
                        v_isShared_1991_ = v_isSharedCheck_1995_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1970_) == 1 {
                    lean_dec(v_a_1968_);
                    v_val_1974_ = lean_ctor_get(v_a_1970_, 0);
                    lean_inc(v_val_1974_);
                    lean_dec_ref_known(v_a_1970_, 1);
                    if v_isShared_1973_ == 0 {
                        lean_ctor_set(v___x_1972_, 0, v_val_1974_);
                        v___x_1976_ = v___x_1972_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_val_1974_);
                        v___x_1976_ = v_reuseFailAlloc_1977_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1972_);
                    lean_dec(v_a_1970_);
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
                    v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
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
                    v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
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
    mut v_e_1996_: *mut LeanObject,
    mut v___y_1997_: *mut LeanObject,
    mut v___y_1998_: *mut LeanObject,
    mut v___y_1999_: *mut LeanObject,
    mut v___y_2000_: *mut LeanObject,
    mut v___y_2001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2002_: *mut LeanObject = core::ptr::null_mut();
    v_res_2002_ = l_Lean_Meta_instReduceEvalNat___lam__0(
        v_e_1996_,
        v___y_1997_,
        v___y_1998_,
        v___y_1999_,
        v___y_2000_,
    );
    lean_dec(v___y_2000_);
    lean_dec_ref(v___y_1999_);
    lean_dec(v___y_1998_);
    lean_dec_ref(v___y_1997_);
    return v_res_2002_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalOption___private__1___redArg(
    mut v_inst_2014_: *mut LeanObject,
    mut v_e_2015_: *mut LeanObject,
    mut v_a_2016_: *mut LeanObject,
    mut v_a_2017_: *mut LeanObject,
    mut v_a_2018_: *mut LeanObject,
    mut v_a_2019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2025_: u8 = 0;
    let mut v___y_2027_: u8 = 0;
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2034_: u8 = 0;
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2039_: u8 = 0;
    let mut v_a_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2043_: u8 = 0;
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2047_: u8 = 0;
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2052_: u8 = 0;
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: u8 = 0;
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: u8 = 0;
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: u8 = 0;
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: u8 = 0;
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2066_: u8 = 0;
    let mut v_a_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2070_: u8 = 0;
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2074_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_2019_);
                lean_inc_ref(v_a_2018_);
                lean_inc(v_a_2017_);
                lean_inc_ref(v_a_2016_);
                v___x_2021_ = lean_whnf(v_e_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
                if lean_obj_tag(v___x_2021_) == 0 {
                    v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
                    v_isSharedCheck_2066_ = (!lean_is_exclusive(v___x_2021_)) as u8;
                    if v_isSharedCheck_2066_ == 0 {
                        v___x_2024_ = v___x_2021_;
                        v_isShared_2025_ = v_isSharedCheck_2066_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2022_);
                        lean_dec(v___x_2021_);
                        v___x_2024_ = lean_box(0);
                        v_isShared_2025_ = v_isSharedCheck_2066_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_inst_2014_);
                    v_a_2067_ = lean_ctor_get(v___x_2021_, 0);
                    v_isSharedCheck_2074_ = (!lean_is_exclusive(v___x_2021_)) as u8;
                    if v_isSharedCheck_2074_ == 0 {
                        v___x_2069_ = v___x_2021_;
                        v_isShared_2070_ = v_isSharedCheck_2074_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2067_);
                        lean_dec(v___x_2021_);
                        v___x_2069_ = lean_box(0);
                        v_isShared_2070_ = v_isSharedCheck_2074_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2048_ = l_Lean_Expr_getAppFn(v_a_2022_);
                if lean_obj_tag(v___x_2048_) == 4 {
                    v_declName_2049_ = lean_ctor_get(v___x_2048_, 0);
                    lean_inc(v_declName_2049_);
                    lean_dec_ref_known(v___x_2048_, 2);
                    v___x_2050_ = l_Lean_Expr_getAppNumArgs(v_a_2022_);
                    v___x_2061_ =
                        l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4;
                    v___x_2062_ = lean_name_eq(v_declName_2049_, v___x_2061_);
                    if v___x_2062_ == 0 {
                        v___y_2052_ = v___x_2062_;
                        state = 7;
                        continue;
                    } else {
                        v___x_2063_ = lean_unsigned_to_nat(0);
                        v___x_2064_ = lean_nat_dec_eq(v___x_2050_, v___x_2063_);
                        v___y_2052_ = v___x_2064_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_2048_);
                    lean_del_object(v___x_2024_);
                    lean_dec_ref(v_inst_2014_);
                    v___x_2065_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_a_2022_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_,
                        );
                    return v___x_2065_;
                }
            }
            2 => {
                if v___y_2027_ == 0 {
                    lean_dec_ref(v_inst_2014_);
                    v___x_2028_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_a_2022_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_,
                        );
                    return v___x_2028_;
                } else {
                    v___x_2029_ = l_Lean_Expr_appArg_x21(v_a_2022_);
                    lean_dec(v_a_2022_);
                    v___x_2030_ = l_Lean_Meta_reduceEval___redArg(
                        v_inst_2014_,
                        v___x_2029_,
                        v_a_2016_,
                        v_a_2017_,
                        v_a_2018_,
                        v_a_2019_,
                    );
                    if lean_obj_tag(v___x_2030_) == 0 {
                        v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
                        v_isSharedCheck_2039_ = (!lean_is_exclusive(v___x_2030_)) as u8;
                        if v_isSharedCheck_2039_ == 0 {
                            v___x_2033_ = v___x_2030_;
                            v_isShared_2034_ = v_isSharedCheck_2039_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2031_);
                            lean_dec(v___x_2030_);
                            v___x_2033_ = lean_box(0);
                            v_isShared_2034_ = v_isSharedCheck_2039_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2040_ = lean_ctor_get(v___x_2030_, 0);
                        v_isSharedCheck_2047_ = (!lean_is_exclusive(v___x_2030_)) as u8;
                        if v_isSharedCheck_2047_ == 0 {
                            v___x_2042_ = v___x_2030_;
                            v_isShared_2043_ = v_isSharedCheck_2047_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_2040_);
                            lean_dec(v___x_2030_);
                            v___x_2042_ = lean_box(0);
                            v_isShared_2043_ = v_isSharedCheck_2047_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_2035_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2035_, 0, v_a_2031_);
                if v_isShared_2034_ == 0 {
                    lean_ctor_set(v___x_2033_, 0, v___x_2035_);
                    v___x_2037_ = v___x_2033_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
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
                    v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
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
                    lean_del_object(v___x_2024_);
                    v___x_2053_ =
                        l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2;
                    v___x_2054_ = lean_name_eq(v_declName_2049_, v___x_2053_);
                    lean_dec(v_declName_2049_);
                    if v___x_2054_ == 0 {
                        lean_dec(v___x_2050_);
                        v___y_2027_ = v___x_2054_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2055_ = lean_unsigned_to_nat(1);
                        v___x_2056_ = lean_nat_dec_eq(v___x_2050_, v___x_2055_);
                        lean_dec(v___x_2050_);
                        v___y_2027_ = v___x_2056_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2050_);
                    lean_dec(v_declName_2049_);
                    lean_dec(v_a_2022_);
                    lean_dec_ref(v_inst_2014_);
                    v___x_2057_ = lean_box(0);
                    if v_isShared_2025_ == 0 {
                        lean_ctor_set(v___x_2024_, 0, v___x_2057_);
                        v___x_2059_ = v___x_2024_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2057_);
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
                    v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
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
    mut v_inst_2075_: *mut LeanObject,
    mut v_e_2076_: *mut LeanObject,
    mut v_a_2077_: *mut LeanObject,
    mut v_a_2078_: *mut LeanObject,
    mut v_a_2079_: *mut LeanObject,
    mut v_a_2080_: *mut LeanObject,
    mut v_a_2081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2082_: *mut LeanObject = core::ptr::null_mut();
    v_res_2082_ = l_Lean_Meta_instReduceEvalOption___private__1___redArg(
        v_inst_2075_,
        v_e_2076_,
        v_a_2077_,
        v_a_2078_,
        v_a_2079_,
        v_a_2080_,
    );
    lean_dec(v_a_2080_);
    lean_dec_ref(v_a_2079_);
    lean_dec(v_a_2078_);
    lean_dec_ref(v_a_2077_);
    return v_res_2082_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalOption___private__1(
    mut v_00_u03b1_2083_: *mut LeanObject,
    mut v_inst_2084_: *mut LeanObject,
    mut v_e_2085_: *mut LeanObject,
    mut v_a_2086_: *mut LeanObject,
    mut v_a_2087_: *mut LeanObject,
    mut v_a_2088_: *mut LeanObject,
    mut v_a_2089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2095_: u8 = 0;
    let mut v___y_2097_: u8 = 0;
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2104_: u8 = 0;
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2109_: u8 = 0;
    let mut v_a_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2113_: u8 = 0;
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2117_: u8 = 0;
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2122_: u8 = 0;
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: u8 = 0;
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: u8 = 0;
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: u8 = 0;
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: u8 = 0;
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2136_: u8 = 0;
    let mut v_a_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2140_: u8 = 0;
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2144_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_2089_);
                lean_inc_ref(v_a_2088_);
                lean_inc(v_a_2087_);
                lean_inc_ref(v_a_2086_);
                v___x_2091_ = lean_whnf(v_e_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
                if lean_obj_tag(v___x_2091_) == 0 {
                    v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
                    v_isSharedCheck_2136_ = (!lean_is_exclusive(v___x_2091_)) as u8;
                    if v_isSharedCheck_2136_ == 0 {
                        v___x_2094_ = v___x_2091_;
                        v_isShared_2095_ = v_isSharedCheck_2136_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2092_);
                        lean_dec(v___x_2091_);
                        v___x_2094_ = lean_box(0);
                        v_isShared_2095_ = v_isSharedCheck_2136_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_inst_2084_);
                    v_a_2137_ = lean_ctor_get(v___x_2091_, 0);
                    v_isSharedCheck_2144_ = (!lean_is_exclusive(v___x_2091_)) as u8;
                    if v_isSharedCheck_2144_ == 0 {
                        v___x_2139_ = v___x_2091_;
                        v_isShared_2140_ = v_isSharedCheck_2144_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2137_);
                        lean_dec(v___x_2091_);
                        v___x_2139_ = lean_box(0);
                        v_isShared_2140_ = v_isSharedCheck_2144_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2118_ = l_Lean_Expr_getAppFn(v_a_2092_);
                if lean_obj_tag(v___x_2118_) == 4 {
                    v_declName_2119_ = lean_ctor_get(v___x_2118_, 0);
                    lean_inc(v_declName_2119_);
                    lean_dec_ref_known(v___x_2118_, 2);
                    v___x_2120_ = l_Lean_Expr_getAppNumArgs(v_a_2092_);
                    v___x_2131_ =
                        l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4;
                    v___x_2132_ = lean_name_eq(v_declName_2119_, v___x_2131_);
                    if v___x_2132_ == 0 {
                        v___y_2122_ = v___x_2132_;
                        state = 7;
                        continue;
                    } else {
                        v___x_2133_ = lean_unsigned_to_nat(0);
                        v___x_2134_ = lean_nat_dec_eq(v___x_2120_, v___x_2133_);
                        v___y_2122_ = v___x_2134_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_2118_);
                    lean_del_object(v___x_2094_);
                    lean_dec_ref(v_inst_2084_);
                    v___x_2135_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_a_2092_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_,
                        );
                    return v___x_2135_;
                }
            }
            2 => {
                if v___y_2097_ == 0 {
                    lean_dec_ref(v_inst_2084_);
                    v___x_2098_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_a_2092_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_,
                        );
                    return v___x_2098_;
                } else {
                    v___x_2099_ = l_Lean_Expr_appArg_x21(v_a_2092_);
                    lean_dec(v_a_2092_);
                    v___x_2100_ = l_Lean_Meta_reduceEval___redArg(
                        v_inst_2084_,
                        v___x_2099_,
                        v_a_2086_,
                        v_a_2087_,
                        v_a_2088_,
                        v_a_2089_,
                    );
                    if lean_obj_tag(v___x_2100_) == 0 {
                        v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
                        v_isSharedCheck_2109_ = (!lean_is_exclusive(v___x_2100_)) as u8;
                        if v_isSharedCheck_2109_ == 0 {
                            v___x_2103_ = v___x_2100_;
                            v_isShared_2104_ = v_isSharedCheck_2109_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2101_);
                            lean_dec(v___x_2100_);
                            v___x_2103_ = lean_box(0);
                            v_isShared_2104_ = v_isSharedCheck_2109_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2110_ = lean_ctor_get(v___x_2100_, 0);
                        v_isSharedCheck_2117_ = (!lean_is_exclusive(v___x_2100_)) as u8;
                        if v_isSharedCheck_2117_ == 0 {
                            v___x_2112_ = v___x_2100_;
                            v_isShared_2113_ = v_isSharedCheck_2117_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_2110_);
                            lean_dec(v___x_2100_);
                            v___x_2112_ = lean_box(0);
                            v_isShared_2113_ = v_isSharedCheck_2117_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_2105_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2105_, 0, v_a_2101_);
                if v_isShared_2104_ == 0 {
                    lean_ctor_set(v___x_2103_, 0, v___x_2105_);
                    v___x_2107_ = v___x_2103_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
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
                    v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
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
                    lean_del_object(v___x_2094_);
                    v___x_2123_ =
                        l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2;
                    v___x_2124_ = lean_name_eq(v_declName_2119_, v___x_2123_);
                    lean_dec(v_declName_2119_);
                    if v___x_2124_ == 0 {
                        lean_dec(v___x_2120_);
                        v___y_2097_ = v___x_2124_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2125_ = lean_unsigned_to_nat(1);
                        v___x_2126_ = lean_nat_dec_eq(v___x_2120_, v___x_2125_);
                        lean_dec(v___x_2120_);
                        v___y_2097_ = v___x_2126_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2120_);
                    lean_dec(v_declName_2119_);
                    lean_dec(v_a_2092_);
                    lean_dec_ref(v_inst_2084_);
                    v___x_2127_ = lean_box(0);
                    if v_isShared_2095_ == 0 {
                        lean_ctor_set(v___x_2094_, 0, v___x_2127_);
                        v___x_2129_ = v___x_2094_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2127_);
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
                    v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
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
    mut v_00_u03b1_2145_: *mut LeanObject,
    mut v_inst_2146_: *mut LeanObject,
    mut v_e_2147_: *mut LeanObject,
    mut v_a_2148_: *mut LeanObject,
    mut v_a_2149_: *mut LeanObject,
    mut v_a_2150_: *mut LeanObject,
    mut v_a_2151_: *mut LeanObject,
    mut v_a_2152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2153_: *mut LeanObject = core::ptr::null_mut();
    v_res_2153_ = l_Lean_Meta_instReduceEvalOption___private__1(
        v_00_u03b1_2145_,
        v_inst_2146_,
        v_e_2147_,
        v_a_2148_,
        v_a_2149_,
        v_a_2150_,
        v_a_2151_,
    );
    lean_dec(v_a_2151_);
    lean_dec_ref(v_a_2150_);
    lean_dec(v_a_2149_);
    lean_dec_ref(v_a_2148_);
    return v_res_2153_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalOption___redArg___lam__0(
    mut v_inst_2154_: *mut LeanObject,
    mut v_e_2155_: *mut LeanObject,
    mut v___y_2156_: *mut LeanObject,
    mut v___y_2157_: *mut LeanObject,
    mut v___y_2158_: *mut LeanObject,
    mut v___y_2159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2165_: u8 = 0;
    let mut v___y_2167_: u8 = 0;
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2174_: u8 = 0;
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2179_: u8 = 0;
    let mut v_a_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2183_: u8 = 0;
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2187_: u8 = 0;
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2192_: u8 = 0;
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: u8 = 0;
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: u8 = 0;
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: u8 = 0;
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: u8 = 0;
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2206_: u8 = 0;
    let mut v_a_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2210_: u8 = 0;
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2214_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_2159_);
                lean_inc_ref(v___y_2158_);
                lean_inc(v___y_2157_);
                lean_inc_ref(v___y_2156_);
                v___x_2161_ = lean_whnf(
                    v_e_2155_,
                    v___y_2156_,
                    v___y_2157_,
                    v___y_2158_,
                    v___y_2159_,
                );
                if lean_obj_tag(v___x_2161_) == 0 {
                    v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
                    v_isSharedCheck_2206_ = (!lean_is_exclusive(v___x_2161_)) as u8;
                    if v_isSharedCheck_2206_ == 0 {
                        v___x_2164_ = v___x_2161_;
                        v_isShared_2165_ = v_isSharedCheck_2206_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2162_);
                        lean_dec(v___x_2161_);
                        v___x_2164_ = lean_box(0);
                        v_isShared_2165_ = v_isSharedCheck_2206_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_inst_2154_);
                    v_a_2207_ = lean_ctor_get(v___x_2161_, 0);
                    v_isSharedCheck_2214_ = (!lean_is_exclusive(v___x_2161_)) as u8;
                    if v_isSharedCheck_2214_ == 0 {
                        v___x_2209_ = v___x_2161_;
                        v_isShared_2210_ = v_isSharedCheck_2214_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2207_);
                        lean_dec(v___x_2161_);
                        v___x_2209_ = lean_box(0);
                        v_isShared_2210_ = v_isSharedCheck_2214_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2188_ = l_Lean_Expr_getAppFn(v_a_2162_);
                if lean_obj_tag(v___x_2188_) == 4 {
                    v_declName_2189_ = lean_ctor_get(v___x_2188_, 0);
                    lean_inc(v_declName_2189_);
                    lean_dec_ref_known(v___x_2188_, 2);
                    v___x_2190_ = l_Lean_Expr_getAppNumArgs(v_a_2162_);
                    v___x_2201_ =
                        l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__4;
                    v___x_2202_ = lean_name_eq(v_declName_2189_, v___x_2201_);
                    if v___x_2202_ == 0 {
                        v___y_2192_ = v___x_2202_;
                        state = 7;
                        continue;
                    } else {
                        v___x_2203_ = lean_unsigned_to_nat(0);
                        v___x_2204_ = lean_nat_dec_eq(v___x_2190_, v___x_2203_);
                        v___y_2192_ = v___x_2204_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_2188_);
                    lean_del_object(v___x_2164_);
                    lean_dec_ref(v_inst_2154_);
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
                    lean_dec_ref(v_inst_2154_);
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
                    lean_dec(v_a_2162_);
                    v___x_2170_ = l_Lean_Meta_reduceEval___redArg(
                        v_inst_2154_,
                        v___x_2169_,
                        v___y_2156_,
                        v___y_2157_,
                        v___y_2158_,
                        v___y_2159_,
                    );
                    if lean_obj_tag(v___x_2170_) == 0 {
                        v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
                        v_isSharedCheck_2179_ = (!lean_is_exclusive(v___x_2170_)) as u8;
                        if v_isSharedCheck_2179_ == 0 {
                            v___x_2173_ = v___x_2170_;
                            v_isShared_2174_ = v_isSharedCheck_2179_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2171_);
                            lean_dec(v___x_2170_);
                            v___x_2173_ = lean_box(0);
                            v_isShared_2174_ = v_isSharedCheck_2179_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2180_ = lean_ctor_get(v___x_2170_, 0);
                        v_isSharedCheck_2187_ = (!lean_is_exclusive(v___x_2170_)) as u8;
                        if v_isSharedCheck_2187_ == 0 {
                            v___x_2182_ = v___x_2170_;
                            v_isShared_2183_ = v_isSharedCheck_2187_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_2180_);
                            lean_dec(v___x_2170_);
                            v___x_2182_ = lean_box(0);
                            v_isShared_2183_ = v_isSharedCheck_2187_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_2175_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2175_, 0, v_a_2171_);
                if v_isShared_2174_ == 0 {
                    lean_ctor_set(v___x_2173_, 0, v___x_2175_);
                    v___x_2177_ = v___x_2173_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2175_);
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
                    v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
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
                    lean_del_object(v___x_2164_);
                    v___x_2193_ =
                        l_Lean_Meta_instReduceEvalOption___private__1___redArg___closed__2;
                    v___x_2194_ = lean_name_eq(v_declName_2189_, v___x_2193_);
                    lean_dec(v_declName_2189_);
                    if v___x_2194_ == 0 {
                        lean_dec(v___x_2190_);
                        v___y_2167_ = v___x_2194_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2195_ = lean_unsigned_to_nat(1);
                        v___x_2196_ = lean_nat_dec_eq(v___x_2190_, v___x_2195_);
                        lean_dec(v___x_2190_);
                        v___y_2167_ = v___x_2196_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2190_);
                    lean_dec(v_declName_2189_);
                    lean_dec(v_a_2162_);
                    lean_dec_ref(v_inst_2154_);
                    v___x_2197_ = lean_box(0);
                    if v_isShared_2165_ == 0 {
                        lean_ctor_set(v___x_2164_, 0, v___x_2197_);
                        v___x_2199_ = v___x_2164_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
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
                    v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
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
    mut v_inst_2215_: *mut LeanObject,
    mut v_e_2216_: *mut LeanObject,
    mut v___y_2217_: *mut LeanObject,
    mut v___y_2218_: *mut LeanObject,
    mut v___y_2219_: *mut LeanObject,
    mut v___y_2220_: *mut LeanObject,
    mut v___y_2221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2222_: *mut LeanObject = core::ptr::null_mut();
    v_res_2222_ = l_Lean_Meta_instReduceEvalOption___redArg___lam__0(
        v_inst_2215_,
        v_e_2216_,
        v___y_2217_,
        v___y_2218_,
        v___y_2219_,
        v___y_2220_,
    );
    lean_dec(v___y_2220_);
    lean_dec_ref(v___y_2219_);
    lean_dec(v___y_2218_);
    lean_dec_ref(v___y_2217_);
    return v_res_2222_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalOption___redArg(
    mut v_inst_2223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2224_: *mut LeanObject = core::ptr::null_mut();
    v___f_2224_ = lean_alloc_closure(
        l_Lean_Meta_instReduceEvalOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___f_2224_, 0, v_inst_2223_);
    return v___f_2224_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalOption(
    mut v_00_u03b1_2225_: *mut LeanObject,
    mut v_inst_2226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2227_: *mut LeanObject = core::ptr::null_mut();
    v___f_2227_ = lean_alloc_closure(
        l_Lean_Meta_instReduceEvalOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___f_2227_, 0, v_inst_2226_);
    return v___f_2227_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalString___private__1(
    mut v_e_2228_: *mut LeanObject,
    mut v_a_2229_: *mut LeanObject,
    mut v_a_2230_: *mut LeanObject,
    mut v_a_2231_: *mut LeanObject,
    mut v_a_2232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2238_: u8 = 0;
    let mut v_a_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2246_: u8 = 0;
    let mut v_a_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2250_: u8 = 0;
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2254_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_2232_);
                lean_inc_ref(v_a_2231_);
                lean_inc(v_a_2230_);
                lean_inc_ref(v_a_2229_);
                lean_inc_ref(v_e_2228_);
                v___x_2234_ = lean_whnf(v_e_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
                if lean_obj_tag(v___x_2234_) == 0 {
                    v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
                    v_isSharedCheck_2246_ = (!lean_is_exclusive(v___x_2234_)) as u8;
                    if v_isSharedCheck_2246_ == 0 {
                        v___x_2237_ = v___x_2234_;
                        v_isShared_2238_ = v_isSharedCheck_2246_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2235_);
                        lean_dec(v___x_2234_);
                        v___x_2237_ = lean_box(0);
                        v_isShared_2238_ = v_isSharedCheck_2246_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_2228_);
                    v_a_2247_ = lean_ctor_get(v___x_2234_, 0);
                    v_isSharedCheck_2254_ = (!lean_is_exclusive(v___x_2234_)) as u8;
                    if v_isSharedCheck_2254_ == 0 {
                        v___x_2249_ = v___x_2234_;
                        v_isShared_2250_ = v_isSharedCheck_2254_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2247_);
                        lean_dec(v___x_2234_);
                        v___x_2249_ = lean_box(0);
                        v_isShared_2250_ = v_isSharedCheck_2254_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2235_) == 9 {
                    v_a_2239_ = lean_ctor_get(v_a_2235_, 0);
                    lean_inc_ref(v_a_2239_);
                    lean_dec_ref_known(v_a_2235_, 1);
                    if lean_obj_tag(v_a_2239_) == 1 {
                        lean_dec_ref(v_e_2228_);
                        v_val_2240_ = lean_ctor_get(v_a_2239_, 0);
                        lean_inc_ref(v_val_2240_);
                        lean_dec_ref_known(v_a_2239_, 1);
                        if v_isShared_2238_ == 0 {
                            lean_ctor_set(v___x_2237_, 0, v_val_2240_);
                            v___x_2242_ = v___x_2237_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_val_2240_);
                            v___x_2242_ = v_reuseFailAlloc_2243_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_a_2239_);
                        lean_del_object(v___x_2237_);
                        v___x_2244_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
                        return v___x_2244_;
                    }
                } else {
                    lean_del_object(v___x_2237_);
                    lean_dec(v_a_2235_);
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
                    v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
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
    mut v_e_2255_: *mut LeanObject,
    mut v_a_2256_: *mut LeanObject,
    mut v_a_2257_: *mut LeanObject,
    mut v_a_2258_: *mut LeanObject,
    mut v_a_2259_: *mut LeanObject,
    mut v_a_2260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2261_: *mut LeanObject = core::ptr::null_mut();
    v_res_2261_ = l_Lean_Meta_instReduceEvalString___private__1(
        v_e_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_,
    );
    lean_dec(v_a_2259_);
    lean_dec_ref(v_a_2258_);
    lean_dec(v_a_2257_);
    lean_dec_ref(v_a_2256_);
    return v_res_2261_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalString___lam__0(
    mut v_e_2262_: *mut LeanObject,
    mut v___y_2263_: *mut LeanObject,
    mut v___y_2264_: *mut LeanObject,
    mut v___y_2265_: *mut LeanObject,
    mut v___y_2266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2272_: u8 = 0;
    let mut v_a_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2280_: u8 = 0;
    let mut v_a_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2284_: u8 = 0;
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_2266_);
                lean_inc_ref(v___y_2265_);
                lean_inc(v___y_2264_);
                lean_inc_ref(v___y_2263_);
                lean_inc_ref(v_e_2262_);
                v___x_2268_ = lean_whnf(
                    v_e_2262_,
                    v___y_2263_,
                    v___y_2264_,
                    v___y_2265_,
                    v___y_2266_,
                );
                if lean_obj_tag(v___x_2268_) == 0 {
                    v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
                    v_isSharedCheck_2280_ = (!lean_is_exclusive(v___x_2268_)) as u8;
                    if v_isSharedCheck_2280_ == 0 {
                        v___x_2271_ = v___x_2268_;
                        v_isShared_2272_ = v_isSharedCheck_2280_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2269_);
                        lean_dec(v___x_2268_);
                        v___x_2271_ = lean_box(0);
                        v_isShared_2272_ = v_isSharedCheck_2280_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_2262_);
                    v_a_2281_ = lean_ctor_get(v___x_2268_, 0);
                    v_isSharedCheck_2288_ = (!lean_is_exclusive(v___x_2268_)) as u8;
                    if v_isSharedCheck_2288_ == 0 {
                        v___x_2283_ = v___x_2268_;
                        v_isShared_2284_ = v_isSharedCheck_2288_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2281_);
                        lean_dec(v___x_2268_);
                        v___x_2283_ = lean_box(0);
                        v_isShared_2284_ = v_isSharedCheck_2288_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2269_) == 9 {
                    v_a_2273_ = lean_ctor_get(v_a_2269_, 0);
                    lean_inc_ref(v_a_2273_);
                    lean_dec_ref_known(v_a_2269_, 1);
                    if lean_obj_tag(v_a_2273_) == 1 {
                        lean_dec_ref(v_e_2262_);
                        v_val_2274_ = lean_ctor_get(v_a_2273_, 0);
                        lean_inc_ref(v_val_2274_);
                        lean_dec_ref_known(v_a_2273_, 1);
                        if v_isShared_2272_ == 0 {
                            lean_ctor_set(v___x_2271_, 0, v_val_2274_);
                            v___x_2276_ = v___x_2271_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_val_2274_);
                            v___x_2276_ = v_reuseFailAlloc_2277_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_a_2273_);
                        lean_del_object(v___x_2271_);
                        v___x_2278_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
                        return v___x_2278_;
                    }
                } else {
                    lean_del_object(v___x_2271_);
                    lean_dec(v_a_2269_);
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
                    v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
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
    mut v_e_2289_: *mut LeanObject,
    mut v___y_2290_: *mut LeanObject,
    mut v___y_2291_: *mut LeanObject,
    mut v___y_2292_: *mut LeanObject,
    mut v___y_2293_: *mut LeanObject,
    mut v___y_2294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2295_: *mut LeanObject = core::ptr::null_mut();
    v_res_2295_ = l_Lean_Meta_instReduceEvalString___lam__0(
        v_e_2289_,
        v___y_2290_,
        v___y_2291_,
        v___y_2292_,
        v___y_2293_,
    );
    lean_dec(v___y_2293_);
    lean_dec_ref(v___y_2292_);
    lean_dec(v___y_2291_);
    lean_dec_ref(v___y_2290_);
    return v_res_2295_;
}
pub unsafe fn l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(
    mut v_e_2298_: *mut LeanObject,
    mut v_a_2299_: *mut LeanObject,
    mut v_a_2300_: *mut LeanObject,
    mut v_a_2301_: *mut LeanObject,
    mut v_a_2302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2305_: u8 = 0;
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2327_: u8 = 0;
    let mut v_trackZetaDelta_2328_: u8 = 0;
    let mut v_zetaDeltaSet_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2335_: u8 = 0;
    let mut v_inTypeClassResolution_2336_: u8 = 0;
    let mut v_cacheInferType_2337_: u8 = 0;
    let mut v_config_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: u64 = 0;
    let mut v___x_2341_: u64 = 0;
    let mut v___x_2342_: u64 = 0;
    let mut v___x_2343_: u64 = 0;
    let mut v___x_2344_: u64 = 0;
    let mut v_key_2345_: u64 = 0;
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2354_: u8 = 0;
    let mut v_val_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2360_: u8 = 0;
    let mut v_a_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2364_: u8 = 0;
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2368_: u8 = 0;
    let mut v_a_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2372_: u8 = 0;
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2376_: u8 = 0;
    let mut v_reuseFailAlloc_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2378_: u8 = 0;
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transparency_2380_: u8 = 0;
    let mut v___x_2381_: u8 = 0;
    let mut v___x_2382_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2379_ = l_Lean_Meta_Context_config(v_a_2299_);
                v_transparency_2380_ = lean_ctor_get_uint8(v___x_2379_, 9 as u32);
                lean_dec_ref(v___x_2379_);
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
                v_foApprox_2307_ = lean_ctor_get_uint8(v___x_2306_, 0 as u32);
                v_ctxApprox_2308_ = lean_ctor_get_uint8(v___x_2306_, 1 as u32);
                v_quasiPatternApprox_2309_ = lean_ctor_get_uint8(v___x_2306_, 2 as u32);
                v_constApprox_2310_ = lean_ctor_get_uint8(v___x_2306_, 3 as u32);
                v_isDefEqStuckEx_2311_ = lean_ctor_get_uint8(v___x_2306_, 4 as u32);
                v_unificationHints_2312_ = lean_ctor_get_uint8(v___x_2306_, 5 as u32);
                v_proofIrrelevance_2313_ = lean_ctor_get_uint8(v___x_2306_, 6 as u32);
                v_assignSyntheticOpaque_2314_ = lean_ctor_get_uint8(v___x_2306_, 7 as u32);
                v_offsetCnstrs_2315_ = lean_ctor_get_uint8(v___x_2306_, 8 as u32);
                v_etaStruct_2316_ = lean_ctor_get_uint8(v___x_2306_, 10 as u32);
                v_univApprox_2317_ = lean_ctor_get_uint8(v___x_2306_, 11 as u32);
                v_iota_2318_ = lean_ctor_get_uint8(v___x_2306_, 12 as u32);
                v_beta_2319_ = lean_ctor_get_uint8(v___x_2306_, 13 as u32);
                v_proj_2320_ = lean_ctor_get_uint8(v___x_2306_, 14 as u32);
                v_zeta_2321_ = lean_ctor_get_uint8(v___x_2306_, 15 as u32);
                v_zetaDelta_2322_ = lean_ctor_get_uint8(v___x_2306_, 16 as u32);
                v_zetaUnused_2323_ = lean_ctor_get_uint8(v___x_2306_, 17 as u32);
                v_zetaHave_2324_ = lean_ctor_get_uint8(v___x_2306_, 18 as u32);
                v_isSharedCheck_2378_ = (!lean_is_exclusive(v___x_2306_)) as u8;
                if v_isSharedCheck_2378_ == 0 {
                    v___x_2326_ = v___x_2306_;
                    v_isShared_2327_ = v_isSharedCheck_2378_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_2306_);
                    v___x_2326_ = lean_box(0);
                    v_isShared_2327_ = v_isSharedCheck_2378_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_trackZetaDelta_2328_ = lean_ctor_get_uint8(
                    v_a_2299_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2329_ = lean_ctor_get(v_a_2299_, 1);
                v_lctx_2330_ = lean_ctor_get(v_a_2299_, 2);
                v_localInstances_2331_ = lean_ctor_get(v_a_2299_, 3);
                v_defEqCtx_x3f_2332_ = lean_ctor_get(v_a_2299_, 4);
                v_synthPendingDepth_2333_ = lean_ctor_get(v_a_2299_, 5);
                v_canUnfold_x3f_2334_ = lean_ctor_get(v_a_2299_, 6);
                v_univApprox_2335_ = lean_ctor_get_uint8(
                    v_a_2299_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2336_ = lean_ctor_get_uint8(
                    v_a_2299_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2337_ = lean_ctor_get_uint8(
                    v_a_2299_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_2327_ == 0 {
                    v_config_2339_ = v___x_2326_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2377_, 0 as u32, v_foApprox_2307_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2377_, 1 as u32, v_ctxApprox_2308_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        2 as u32,
                        v_quasiPatternApprox_2309_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_2377_, 3 as u32, v_constApprox_2310_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2377_, 4 as u32, v_isDefEqStuckEx_2311_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2377_, 5 as u32, v_unificationHints_2312_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2377_, 6 as u32, v_proofIrrelevance_2313_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        7 as u32,
                        v_assignSyntheticOpaque_2314_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_2377_, 8 as u32, v_offsetCnstrs_2315_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2377_, 10 as u32, v_etaStruct_2316_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2377_, 11 as u32, v_univApprox_2317_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2377_, 12 as u32, v_iota_2318_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2377_, 13 as u32, v_beta_2319_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2377_, 14 as u32, v_proj_2320_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2377_, 15 as u32, v_zeta_2321_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2377_, 16 as u32, v_zetaDelta_2322_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2377_, 17 as u32, v_zetaUnused_2323_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2377_, 18 as u32, v_zetaHave_2324_);
                    v_config_2339_ = v_reuseFailAlloc_2377_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(v_config_2339_, 9 as u32, v___y_2305_);
                v___x_2340_ = l_Lean_Meta_Context_configKey(v_a_2299_);
                v___x_2341_ = 3u64;
                v___x_2342_ = lean_uint64_shift_right(v___x_2340_, v___x_2341_);
                v___x_2343_ = lean_uint64_shift_left(v___x_2342_, v___x_2341_);
                v___x_2344_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2305_);
                v_key_2345_ = lean_uint64_lor(v___x_2343_, v___x_2344_);
                v___x_2346_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_2346_, 0, v_config_2339_);
                lean_ctor_set_uint64(
                    v___x_2346_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_2345_,
                );
                lean_inc(v_canUnfold_x3f_2334_);
                lean_inc(v_synthPendingDepth_2333_);
                lean_inc(v_defEqCtx_x3f_2332_);
                lean_inc_ref(v_localInstances_2331_);
                lean_inc_ref(v_lctx_2330_);
                lean_inc(v_zetaDeltaSet_2329_);
                v___x_2347_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_2347_, 0, v___x_2346_);
                lean_ctor_set(v___x_2347_, 1, v_zetaDeltaSet_2329_);
                lean_ctor_set(v___x_2347_, 2, v_lctx_2330_);
                lean_ctor_set(v___x_2347_, 3, v_localInstances_2331_);
                lean_ctor_set(v___x_2347_, 4, v_defEqCtx_x3f_2332_);
                lean_ctor_set(v___x_2347_, 5, v_synthPendingDepth_2333_);
                lean_ctor_set(v___x_2347_, 6, v_canUnfold_x3f_2334_);
                lean_ctor_set_uint8(
                    v___x_2347_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2328_,
                );
                lean_ctor_set_uint8(
                    v___x_2347_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2335_,
                );
                lean_ctor_set_uint8(
                    v___x_2347_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2336_,
                );
                lean_ctor_set_uint8(
                    v___x_2347_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2337_,
                );
                lean_inc(v_a_2302_);
                lean_inc_ref(v_a_2301_);
                lean_inc(v_a_2300_);
                lean_inc_ref(v___x_2347_);
                v___x_2348_ = lean_whnf(v_e_2298_, v___x_2347_, v_a_2300_, v_a_2301_, v_a_2302_);
                if lean_obj_tag(v___x_2348_) == 0 {
                    v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
                    lean_inc_n(v_a_2349_, 2);
                    lean_dec_ref_known(v___x_2348_, 1);
                    v___x_2350_ = l_Lean_Meta_evalNat(
                        v_a_2349_,
                        v___x_2347_,
                        v_a_2300_,
                        v_a_2301_,
                        v_a_2302_,
                    );
                    if lean_obj_tag(v___x_2350_) == 0 {
                        v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
                        v_isSharedCheck_2360_ = (!lean_is_exclusive(v___x_2350_)) as u8;
                        if v_isSharedCheck_2360_ == 0 {
                            v___x_2353_ = v___x_2350_;
                            v_isShared_2354_ = v_isSharedCheck_2360_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2351_);
                            lean_dec(v___x_2350_);
                            v___x_2353_ = lean_box(0);
                            v_isShared_2354_ = v_isSharedCheck_2360_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2349_);
                        lean_dec_ref_known(v___x_2347_, 7);
                        v_a_2361_ = lean_ctor_get(v___x_2350_, 0);
                        v_isSharedCheck_2368_ = (!lean_is_exclusive(v___x_2350_)) as u8;
                        if v_isSharedCheck_2368_ == 0 {
                            v___x_2363_ = v___x_2350_;
                            v_isShared_2364_ = v_isSharedCheck_2368_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2361_);
                            lean_dec(v___x_2350_);
                            v___x_2363_ = lean_box(0);
                            v_isShared_2364_ = v_isSharedCheck_2368_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_2347_, 7);
                    v_a_2369_ = lean_ctor_get(v___x_2348_, 0);
                    v_isSharedCheck_2376_ = (!lean_is_exclusive(v___x_2348_)) as u8;
                    if v_isSharedCheck_2376_ == 0 {
                        v___x_2371_ = v___x_2348_;
                        v_isShared_2372_ = v_isSharedCheck_2376_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2369_);
                        lean_dec(v___x_2348_);
                        v___x_2371_ = lean_box(0);
                        v_isShared_2372_ = v_isSharedCheck_2376_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                if lean_obj_tag(v_a_2351_) == 1 {
                    lean_dec(v_a_2349_);
                    lean_dec_ref_known(v___x_2347_, 7);
                    v_val_2355_ = lean_ctor_get(v_a_2351_, 0);
                    lean_inc(v_val_2355_);
                    lean_dec_ref_known(v_a_2351_, 1);
                    if v_isShared_2354_ == 0 {
                        lean_ctor_set(v___x_2353_, 0, v_val_2355_);
                        v___x_2357_ = v___x_2353_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_val_2355_);
                        v___x_2357_ = v_reuseFailAlloc_2358_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2353_);
                    lean_dec(v_a_2351_);
                    v___x_2359_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_a_2349_,
                            v___x_2347_,
                            v_a_2300_,
                            v_a_2301_,
                            v_a_2302_,
                        );
                    lean_dec_ref_known(v___x_2347_, 7);
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
                    v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
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
                    v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
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
    mut v_e_2383_: *mut LeanObject,
    mut v_a_2384_: *mut LeanObject,
    mut v_a_2385_: *mut LeanObject,
    mut v_a_2386_: *mut LeanObject,
    mut v_a_2387_: *mut LeanObject,
    mut v_a_2388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2389_: *mut LeanObject = core::ptr::null_mut();
    v_res_2389_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(v_e_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
    lean_dec(v_a_2387_);
    lean_dec_ref(v_a_2386_);
    lean_dec(v_a_2385_);
    lean_dec_ref(v_a_2384_);
    return v_res_2389_;
}
pub unsafe fn l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(
    mut v_e_2390_: *mut LeanObject,
    mut v_a_2391_: *mut LeanObject,
    mut v_a_2392_: *mut LeanObject,
    mut v_a_2393_: *mut LeanObject,
    mut v_a_2394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2397_: u8 = 0;
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2419_: u8 = 0;
    let mut v_trackZetaDelta_2420_: u8 = 0;
    let mut v_zetaDeltaSet_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2427_: u8 = 0;
    let mut v_inTypeClassResolution_2428_: u8 = 0;
    let mut v_cacheInferType_2429_: u8 = 0;
    let mut v_config_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: u64 = 0;
    let mut v___x_2433_: u64 = 0;
    let mut v___x_2434_: u64 = 0;
    let mut v___x_2435_: u64 = 0;
    let mut v___x_2436_: u64 = 0;
    let mut v_key_2437_: u64 = 0;
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2444_: u8 = 0;
    let mut v_a_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2452_: u8 = 0;
    let mut v_a_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2456_: u8 = 0;
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2460_: u8 = 0;
    let mut v_reuseFailAlloc_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2462_: u8 = 0;
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transparency_2464_: u8 = 0;
    let mut v___x_2465_: u8 = 0;
    let mut v___x_2466_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2463_ = l_Lean_Meta_Context_config(v_a_2391_);
                v_transparency_2464_ = lean_ctor_get_uint8(v___x_2463_, 9 as u32);
                lean_dec_ref(v___x_2463_);
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
                v_foApprox_2399_ = lean_ctor_get_uint8(v___x_2398_, 0 as u32);
                v_ctxApprox_2400_ = lean_ctor_get_uint8(v___x_2398_, 1 as u32);
                v_quasiPatternApprox_2401_ = lean_ctor_get_uint8(v___x_2398_, 2 as u32);
                v_constApprox_2402_ = lean_ctor_get_uint8(v___x_2398_, 3 as u32);
                v_isDefEqStuckEx_2403_ = lean_ctor_get_uint8(v___x_2398_, 4 as u32);
                v_unificationHints_2404_ = lean_ctor_get_uint8(v___x_2398_, 5 as u32);
                v_proofIrrelevance_2405_ = lean_ctor_get_uint8(v___x_2398_, 6 as u32);
                v_assignSyntheticOpaque_2406_ = lean_ctor_get_uint8(v___x_2398_, 7 as u32);
                v_offsetCnstrs_2407_ = lean_ctor_get_uint8(v___x_2398_, 8 as u32);
                v_etaStruct_2408_ = lean_ctor_get_uint8(v___x_2398_, 10 as u32);
                v_univApprox_2409_ = lean_ctor_get_uint8(v___x_2398_, 11 as u32);
                v_iota_2410_ = lean_ctor_get_uint8(v___x_2398_, 12 as u32);
                v_beta_2411_ = lean_ctor_get_uint8(v___x_2398_, 13 as u32);
                v_proj_2412_ = lean_ctor_get_uint8(v___x_2398_, 14 as u32);
                v_zeta_2413_ = lean_ctor_get_uint8(v___x_2398_, 15 as u32);
                v_zetaDelta_2414_ = lean_ctor_get_uint8(v___x_2398_, 16 as u32);
                v_zetaUnused_2415_ = lean_ctor_get_uint8(v___x_2398_, 17 as u32);
                v_zetaHave_2416_ = lean_ctor_get_uint8(v___x_2398_, 18 as u32);
                v_isSharedCheck_2462_ = (!lean_is_exclusive(v___x_2398_)) as u8;
                if v_isSharedCheck_2462_ == 0 {
                    v___x_2418_ = v___x_2398_;
                    v_isShared_2419_ = v_isSharedCheck_2462_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_2398_);
                    v___x_2418_ = lean_box(0);
                    v_isShared_2419_ = v_isSharedCheck_2462_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_trackZetaDelta_2420_ = lean_ctor_get_uint8(
                    v_a_2391_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2421_ = lean_ctor_get(v_a_2391_, 1);
                v_lctx_2422_ = lean_ctor_get(v_a_2391_, 2);
                v_localInstances_2423_ = lean_ctor_get(v_a_2391_, 3);
                v_defEqCtx_x3f_2424_ = lean_ctor_get(v_a_2391_, 4);
                v_synthPendingDepth_2425_ = lean_ctor_get(v_a_2391_, 5);
                v_canUnfold_x3f_2426_ = lean_ctor_get(v_a_2391_, 6);
                v_univApprox_2427_ = lean_ctor_get_uint8(
                    v_a_2391_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2428_ = lean_ctor_get_uint8(
                    v_a_2391_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2429_ = lean_ctor_get_uint8(
                    v_a_2391_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_2419_ == 0 {
                    v_config_2431_ = v___x_2418_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 0 as u32, v_foApprox_2399_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 1 as u32, v_ctxApprox_2400_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2461_,
                        2 as u32,
                        v_quasiPatternApprox_2401_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 3 as u32, v_constApprox_2402_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 4 as u32, v_isDefEqStuckEx_2403_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 5 as u32, v_unificationHints_2404_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 6 as u32, v_proofIrrelevance_2405_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2461_,
                        7 as u32,
                        v_assignSyntheticOpaque_2406_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 8 as u32, v_offsetCnstrs_2407_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 10 as u32, v_etaStruct_2408_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 11 as u32, v_univApprox_2409_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 12 as u32, v_iota_2410_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 13 as u32, v_beta_2411_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 14 as u32, v_proj_2412_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 15 as u32, v_zeta_2413_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 16 as u32, v_zetaDelta_2414_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 17 as u32, v_zetaUnused_2415_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2461_, 18 as u32, v_zetaHave_2416_);
                    v_config_2431_ = v_reuseFailAlloc_2461_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(v_config_2431_, 9 as u32, v___y_2397_);
                v___x_2432_ = l_Lean_Meta_Context_configKey(v_a_2391_);
                v___x_2433_ = 3u64;
                v___x_2434_ = lean_uint64_shift_right(v___x_2432_, v___x_2433_);
                v___x_2435_ = lean_uint64_shift_left(v___x_2434_, v___x_2433_);
                v___x_2436_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2397_);
                v_key_2437_ = lean_uint64_lor(v___x_2435_, v___x_2436_);
                v___x_2438_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_2438_, 0, v_config_2431_);
                lean_ctor_set_uint64(
                    v___x_2438_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_2437_,
                );
                lean_inc(v_canUnfold_x3f_2426_);
                lean_inc(v_synthPendingDepth_2425_);
                lean_inc(v_defEqCtx_x3f_2424_);
                lean_inc_ref(v_localInstances_2423_);
                lean_inc_ref(v_lctx_2422_);
                lean_inc(v_zetaDeltaSet_2421_);
                v___x_2439_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_2439_, 0, v___x_2438_);
                lean_ctor_set(v___x_2439_, 1, v_zetaDeltaSet_2421_);
                lean_ctor_set(v___x_2439_, 2, v_lctx_2422_);
                lean_ctor_set(v___x_2439_, 3, v_localInstances_2423_);
                lean_ctor_set(v___x_2439_, 4, v_defEqCtx_x3f_2424_);
                lean_ctor_set(v___x_2439_, 5, v_synthPendingDepth_2425_);
                lean_ctor_set(v___x_2439_, 6, v_canUnfold_x3f_2426_);
                lean_ctor_set_uint8(
                    v___x_2439_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2420_,
                );
                lean_ctor_set_uint8(
                    v___x_2439_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2427_,
                );
                lean_ctor_set_uint8(
                    v___x_2439_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2428_,
                );
                lean_ctor_set_uint8(
                    v___x_2439_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2429_,
                );
                lean_inc(v_a_2394_);
                lean_inc_ref(v_a_2393_);
                lean_inc(v_a_2392_);
                lean_inc_ref(v___x_2439_);
                lean_inc_ref(v_e_2390_);
                v___x_2440_ = lean_whnf(v_e_2390_, v___x_2439_, v_a_2392_, v_a_2393_, v_a_2394_);
                if lean_obj_tag(v___x_2440_) == 0 {
                    v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
                    v_isSharedCheck_2452_ = (!lean_is_exclusive(v___x_2440_)) as u8;
                    if v_isSharedCheck_2452_ == 0 {
                        v___x_2443_ = v___x_2440_;
                        v_isShared_2444_ = v_isSharedCheck_2452_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2441_);
                        lean_dec(v___x_2440_);
                        v___x_2443_ = lean_box(0);
                        v_isShared_2444_ = v_isSharedCheck_2452_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_2439_, 7);
                    lean_dec_ref(v_e_2390_);
                    v_a_2453_ = lean_ctor_get(v___x_2440_, 0);
                    v_isSharedCheck_2460_ = (!lean_is_exclusive(v___x_2440_)) as u8;
                    if v_isSharedCheck_2460_ == 0 {
                        v___x_2455_ = v___x_2440_;
                        v_isShared_2456_ = v_isSharedCheck_2460_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2453_);
                        lean_dec(v___x_2440_);
                        v___x_2455_ = lean_box(0);
                        v_isShared_2456_ = v_isSharedCheck_2460_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if lean_obj_tag(v_a_2441_) == 9 {
                    v_a_2445_ = lean_ctor_get(v_a_2441_, 0);
                    lean_inc_ref(v_a_2445_);
                    lean_dec_ref_known(v_a_2441_, 1);
                    if lean_obj_tag(v_a_2445_) == 1 {
                        lean_dec_ref_known(v___x_2439_, 7);
                        lean_dec_ref(v_e_2390_);
                        v_val_2446_ = lean_ctor_get(v_a_2445_, 0);
                        lean_inc_ref(v_val_2446_);
                        lean_dec_ref_known(v_a_2445_, 1);
                        if v_isShared_2444_ == 0 {
                            lean_ctor_set(v___x_2443_, 0, v_val_2446_);
                            v___x_2448_ = v___x_2443_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_val_2446_);
                            v___x_2448_ = v_reuseFailAlloc_2449_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_a_2445_);
                        lean_del_object(v___x_2443_);
                        v___x_2450_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_2390_, v___x_2439_, v_a_2392_, v_a_2393_, v_a_2394_);
                        lean_dec_ref_known(v___x_2439_, 7);
                        return v___x_2450_;
                    }
                } else {
                    lean_del_object(v___x_2443_);
                    lean_dec(v_a_2441_);
                    v___x_2451_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_e_2390_,
                            v___x_2439_,
                            v_a_2392_,
                            v_a_2393_,
                            v_a_2394_,
                        );
                    lean_dec_ref_known(v___x_2439_, 7);
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
                    v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
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
    mut v_e_2467_: *mut LeanObject,
    mut v_a_2468_: *mut LeanObject,
    mut v_a_2469_: *mut LeanObject,
    mut v_a_2470_: *mut LeanObject,
    mut v_a_2471_: *mut LeanObject,
    mut v_a_2472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2473_: *mut LeanObject = core::ptr::null_mut();
    v_res_2473_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(v_e_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_);
    lean_dec(v_a_2471_);
    lean_dec_ref(v_a_2470_);
    lean_dec(v_a_2469_);
    lean_dec_ref(v_a_2468_);
    return v_res_2473_;
}
pub unsafe fn l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(
    mut v___x_2474_: *mut LeanObject,
    mut v_00___2475_: *mut LeanObject,
) -> u8 {
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: u8 = 0;
    v___x_2476_ = lean_unsigned_to_nat(2);
    v___x_2477_ = lean_nat_dec_eq(v___x_2474_, v___x_2476_);
    return v___x_2477_;
}
pub unsafe fn l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0___boxed(
    mut v___x_2478_: *mut LeanObject,
    mut v_00___2479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2480_: u8 = 0;
    let mut v_r_2481_: *mut LeanObject = core::ptr::null_mut();
    v_res_2480_ =
        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(v___x_2478_, v_00___2479_);
    lean_dec(v___x_2478_);
    v_r_2481_ = lean_box((v_res_2480_) as usize);
    return v_r_2481_;
}
pub unsafe fn l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(
    mut v_e_2499_: *mut LeanObject,
    mut v_a_2500_: *mut LeanObject,
    mut v_a_2501_: *mut LeanObject,
    mut v_a_2502_: *mut LeanObject,
    mut v_a_2503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2509_: u8 = 0;
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2514_: u8 = 0;
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2527_: u8 = 0;
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2532_: u8 = 0;
    let mut v_a_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2536_: u8 = 0;
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2540_: u8 = 0;
    let mut v___y_2542_: u8 = 0;
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: u8 = 0;
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: u8 = 0;
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2558_: u8 = 0;
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2563_: u8 = 0;
    let mut v_a_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2567_: u8 = 0;
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2571_: u8 = 0;
    let mut v___y_2573_: u8 = 0;
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: u8 = 0;
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: u8 = 0;
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: u8 = 0;
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: u8 = 0;
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2587_: u8 = 0;
    let mut v_a_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2591_: u8 = 0;
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2595_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_2503_);
                lean_inc_ref(v_a_2502_);
                lean_inc(v_a_2501_);
                lean_inc_ref(v_a_2500_);
                v___x_2505_ = lean_whnf(v_e_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
                if lean_obj_tag(v___x_2505_) == 0 {
                    v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
                    v_isSharedCheck_2587_ = (!lean_is_exclusive(v___x_2505_)) as u8;
                    if v_isSharedCheck_2587_ == 0 {
                        v___x_2508_ = v___x_2505_;
                        v_isShared_2509_ = v_isSharedCheck_2587_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2506_);
                        lean_dec(v___x_2505_);
                        v___x_2508_ = lean_box(0);
                        v_isShared_2509_ = v_isSharedCheck_2587_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2588_ = lean_ctor_get(v___x_2505_, 0);
                    v_isSharedCheck_2595_ = (!lean_is_exclusive(v___x_2505_)) as u8;
                    if v_isSharedCheck_2595_ == 0 {
                        v___x_2590_ = v___x_2505_;
                        v_isShared_2591_ = v_isSharedCheck_2595_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_2588_);
                        lean_dec(v___x_2505_);
                        v___x_2590_ = lean_box(0);
                        v_isShared_2591_ = v_isSharedCheck_2595_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2510_ = l_Lean_Expr_getAppFn(v_a_2506_);
                if lean_obj_tag(v___x_2510_) == 4 {
                    v_declName_2511_ = lean_ctor_get(v___x_2510_, 0);
                    lean_inc(v_declName_2511_);
                    lean_dec_ref_known(v___x_2510_, 2);
                    v___x_2512_ = l_Lean_Expr_getAppNumArgs(v_a_2506_);
                    v___x_2582_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7;
                    v___x_2583_ = lean_name_eq(v_declName_2511_, v___x_2582_);
                    if v___x_2583_ == 0 {
                        v___y_2573_ = v___x_2583_;
                        state = 12;
                        continue;
                    } else {
                        v___x_2584_ = lean_unsigned_to_nat(0);
                        v___x_2585_ = lean_nat_dec_eq(v___x_2512_, v___x_2584_);
                        v___y_2573_ = v___x_2585_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_2510_);
                    lean_del_object(v___x_2508_);
                    v___x_2586_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_a_2506_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_,
                        );
                    return v___x_2586_;
                }
            }
            2 => {
                if v___y_2514_ == 0 {
                    lean_dec(v___x_2512_);
                    v___x_2515_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_a_2506_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_,
                        );
                    return v___x_2515_;
                } else {
                    v___x_2516_ = lean_unsigned_to_nat(1);
                    v___x_2517_ = lean_nat_sub(v___x_2512_, v___x_2516_);
                    lean_dec(v___x_2512_);
                    lean_inc(v___x_2517_);
                    v___x_2518_ = l_Lean_Expr_getRevArg_x21(v_a_2506_, v___x_2517_);
                    v___x_2519_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(
                        v___x_2518_,
                        v_a_2500_,
                        v_a_2501_,
                        v_a_2502_,
                        v_a_2503_,
                    );
                    if lean_obj_tag(v___x_2519_) == 0 {
                        v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
                        lean_inc(v_a_2520_);
                        lean_dec_ref_known(v___x_2519_, 1);
                        v___x_2521_ = lean_nat_sub(v___x_2517_, v___x_2516_);
                        lean_dec(v___x_2517_);
                        v___x_2522_ = l_Lean_Expr_getRevArg_x21(v_a_2506_, v___x_2521_);
                        lean_dec(v_a_2506_);
                        v___x_2523_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(v___x_2522_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
                        if lean_obj_tag(v___x_2523_) == 0 {
                            v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
                            v_isSharedCheck_2532_ = (!lean_is_exclusive(v___x_2523_)) as u8;
                            if v_isSharedCheck_2532_ == 0 {
                                v___x_2526_ = v___x_2523_;
                                v_isShared_2527_ = v_isSharedCheck_2532_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_2524_);
                                lean_dec(v___x_2523_);
                                v___x_2526_ = lean_box(0);
                                v_isShared_2527_ = v_isSharedCheck_2532_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2520_);
                            v_a_2533_ = lean_ctor_get(v___x_2523_, 0);
                            v_isSharedCheck_2540_ = (!lean_is_exclusive(v___x_2523_)) as u8;
                            if v_isSharedCheck_2540_ == 0 {
                                v___x_2535_ = v___x_2523_;
                                v_isShared_2536_ = v_isSharedCheck_2540_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_2533_);
                                lean_dec(v___x_2523_);
                                v___x_2535_ = lean_box(0);
                                v_isShared_2536_ = v_isSharedCheck_2540_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_2517_);
                        lean_dec(v_a_2506_);
                        return v___x_2519_;
                    }
                }
            }
            3 => {
                v___x_2528_ = l_Lean_Name_num___override(v_a_2520_, v_a_2524_);
                if v_isShared_2527_ == 0 {
                    lean_ctor_set(v___x_2526_, 0, v___x_2528_);
                    v___x_2530_ = v___x_2526_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
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
                    v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
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
                    lean_dec(v_declName_2511_);
                    if v___x_2544_ == 0 {
                        v___y_2514_ = v___x_2544_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2545_ = lean_box(0);
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
                    lean_dec(v_declName_2511_);
                    v___x_2547_ = lean_unsigned_to_nat(1);
                    v___x_2548_ = lean_nat_sub(v___x_2512_, v___x_2547_);
                    lean_dec(v___x_2512_);
                    lean_inc(v___x_2548_);
                    v___x_2549_ = l_Lean_Expr_getRevArg_x21(v_a_2506_, v___x_2548_);
                    v___x_2550_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(
                        v___x_2549_,
                        v_a_2500_,
                        v_a_2501_,
                        v_a_2502_,
                        v_a_2503_,
                    );
                    if lean_obj_tag(v___x_2550_) == 0 {
                        v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
                        lean_inc(v_a_2551_);
                        lean_dec_ref_known(v___x_2550_, 1);
                        v___x_2552_ = lean_nat_sub(v___x_2548_, v___x_2547_);
                        lean_dec(v___x_2548_);
                        v___x_2553_ = l_Lean_Expr_getRevArg_x21(v_a_2506_, v___x_2552_);
                        lean_dec(v_a_2506_);
                        v___x_2554_ = l_Lean_Meta_reduceEval___at___00__private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(v___x_2553_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
                        if lean_obj_tag(v___x_2554_) == 0 {
                            v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
                            v_isSharedCheck_2563_ = (!lean_is_exclusive(v___x_2554_)) as u8;
                            if v_isSharedCheck_2563_ == 0 {
                                v___x_2557_ = v___x_2554_;
                                v_isShared_2558_ = v_isSharedCheck_2563_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_2555_);
                                lean_dec(v___x_2554_);
                                v___x_2557_ = lean_box(0);
                                v_isShared_2558_ = v_isSharedCheck_2563_;
                                state = 8;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2551_);
                            v_a_2564_ = lean_ctor_get(v___x_2554_, 0);
                            v_isSharedCheck_2571_ = (!lean_is_exclusive(v___x_2554_)) as u8;
                            if v_isSharedCheck_2571_ == 0 {
                                v___x_2566_ = v___x_2554_;
                                v_isShared_2567_ = v_isSharedCheck_2571_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_2564_);
                                lean_dec(v___x_2554_);
                                v___x_2566_ = lean_box(0);
                                v_isShared_2567_ = v_isSharedCheck_2571_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_2548_);
                        lean_dec(v_a_2506_);
                        return v___x_2550_;
                    }
                }
            }
            8 => {
                v___x_2559_ = l_Lean_Name_str___override(v_a_2551_, v_a_2555_);
                if v_isShared_2558_ == 0 {
                    lean_ctor_set(v___x_2557_, 0, v___x_2559_);
                    v___x_2561_ = v___x_2557_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2559_);
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
                    v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
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
                    lean_del_object(v___x_2508_);
                    v___x_2574_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5;
                    v___x_2575_ = lean_name_eq(v_declName_2511_, v___x_2574_);
                    if v___x_2575_ == 0 {
                        v___y_2542_ = v___x_2575_;
                        state = 7;
                        continue;
                    } else {
                        v___x_2576_ = lean_box(0);
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
                    lean_dec(v___x_2512_);
                    lean_dec(v_declName_2511_);
                    lean_dec(v_a_2506_);
                    v___x_2578_ = lean_box(0);
                    if v_isShared_2509_ == 0 {
                        lean_ctor_set(v___x_2508_, 0, v___x_2578_);
                        v___x_2580_ = v___x_2508_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2578_);
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
                    v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
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
    mut v_e_2596_: *mut LeanObject,
    mut v_a_2597_: *mut LeanObject,
    mut v_a_2598_: *mut LeanObject,
    mut v_a_2599_: *mut LeanObject,
    mut v_a_2600_: *mut LeanObject,
    mut v_a_2601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2602_: *mut LeanObject = core::ptr::null_mut();
    v_res_2602_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(
        v_e_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_,
    );
    lean_dec(v_a_2600_);
    lean_dec_ref(v_a_2599_);
    lean_dec(v_a_2598_);
    lean_dec_ref(v_a_2597_);
    return v_res_2602_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalName___private__1(
    mut v_e_2603_: *mut LeanObject,
    mut v_a_2604_: *mut LeanObject,
    mut v_a_2605_: *mut LeanObject,
    mut v_a_2606_: *mut LeanObject,
    mut v_a_2607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    v___x_2609_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(
        v_e_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_,
    );
    return v___x_2609_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalName___private__1___boxed(
    mut v_e_2610_: *mut LeanObject,
    mut v_a_2611_: *mut LeanObject,
    mut v_a_2612_: *mut LeanObject,
    mut v_a_2613_: *mut LeanObject,
    mut v_a_2614_: *mut LeanObject,
    mut v_a_2615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2616_: *mut LeanObject = core::ptr::null_mut();
    v_res_2616_ = l_Lean_Meta_instReduceEvalName___private__1(
        v_e_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_,
    );
    lean_dec(v_a_2614_);
    lean_dec_ref(v_a_2613_);
    lean_dec(v_a_2612_);
    lean_dec_ref(v_a_2611_);
    return v_res_2616_;
}
pub unsafe fn l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(
    mut v_inst_2622_: *mut LeanObject,
    mut v_e_2623_: *mut LeanObject,
    mut v_a_2624_: *mut LeanObject,
    mut v_a_2625_: *mut LeanObject,
    mut v_a_2626_: *mut LeanObject,
    mut v_a_2627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2633_: u8 = 0;
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: u8 = 0;
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: u8 = 0;
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: u8 = 0;
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: u8 = 0;
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2666_: u8 = 0;
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2671_: u8 = 0;
    let mut v_a_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2675_: u8 = 0;
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2679_: u8 = 0;
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: u8 = 0;
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2691_: u8 = 0;
    let mut v_a_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2695_: u8 = 0;
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2699_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_2627_);
                lean_inc_ref(v_a_2626_);
                lean_inc(v_a_2625_);
                lean_inc_ref(v_a_2624_);
                v___x_2629_ = lean_whnf(v_e_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
                if lean_obj_tag(v___x_2629_) == 0 {
                    v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
                    v_isSharedCheck_2691_ = (!lean_is_exclusive(v___x_2629_)) as u8;
                    if v_isSharedCheck_2691_ == 0 {
                        v___x_2632_ = v___x_2629_;
                        v_isShared_2633_ = v_isSharedCheck_2691_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2630_);
                        lean_dec(v___x_2629_);
                        v___x_2632_ = lean_box(0);
                        v_isShared_2633_ = v_isSharedCheck_2691_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_inst_2622_);
                    v_a_2692_ = lean_ctor_get(v___x_2629_, 0);
                    v_isSharedCheck_2699_ = (!lean_is_exclusive(v___x_2629_)) as u8;
                    if v_isSharedCheck_2699_ == 0 {
                        v___x_2694_ = v___x_2629_;
                        v_isShared_2695_ = v_isSharedCheck_2699_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2692_);
                        lean_dec(v___x_2629_);
                        v___x_2694_ = lean_box(0);
                        v_isShared_2695_ = v_isSharedCheck_2699_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2634_ = l_Lean_Expr_getAppFn(v_a_2630_);
                if lean_obj_tag(v___x_2634_) == 4 {
                    v_declName_2635_ = lean_ctor_get(v___x_2634_, 0);
                    lean_inc(v_declName_2635_);
                    lean_dec_ref_known(v___x_2634_, 2);
                    if lean_obj_tag(v_declName_2635_) == 1 {
                        v_pre_2636_ = lean_ctor_get(v_declName_2635_, 0);
                        lean_inc(v_pre_2636_);
                        if lean_obj_tag(v_pre_2636_) == 1 {
                            v_pre_2637_ = lean_ctor_get(v_pre_2636_, 0);
                            if lean_obj_tag(v_pre_2637_) == 0 {
                                v_str_2638_ = lean_ctor_get(v_declName_2635_, 1);
                                lean_inc_ref(v_str_2638_);
                                lean_dec_ref_known(v_declName_2635_, 2);
                                v_str_2639_ = lean_ctor_get(v_pre_2636_, 1);
                                lean_inc_ref(v_str_2639_);
                                lean_dec_ref_known(v_pre_2636_, 2);
                                v___x_2640_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__0;
                                v___x_2641_ = lean_string_dec_eq(v_str_2639_, v___x_2640_);
                                lean_dec_ref(v_str_2639_);
                                if v___x_2641_ == 0 {
                                    lean_dec_ref(v_str_2638_);
                                    lean_del_object(v___x_2632_);
                                    lean_dec_ref(v_inst_2622_);
                                    v___x_2642_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_2630_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
                                    return v___x_2642_;
                                } else {
                                    v___x_2643_ = l_Lean_Expr_getAppNumArgs(v_a_2630_);
                                    v___x_2644_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__1;
                                    v___x_2645_ = lean_string_dec_eq(v_str_2638_, v___x_2644_);
                                    if v___x_2645_ == 0 {
                                        lean_del_object(v___x_2632_);
                                        v___x_2646_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg___closed__2;
                                        v___x_2647_ = lean_string_dec_eq(v_str_2638_, v___x_2646_);
                                        lean_dec_ref(v_str_2638_);
                                        if v___x_2647_ == 0 {
                                            lean_dec(v___x_2643_);
                                            lean_dec_ref(v_inst_2622_);
                                            v___x_2648_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_2630_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
                                            return v___x_2648_;
                                        } else {
                                            v___x_2649_ = lean_unsigned_to_nat(3);
                                            v___x_2650_ = lean_nat_dec_eq(v___x_2643_, v___x_2649_);
                                            if v___x_2650_ == 0 {
                                                lean_dec(v___x_2643_);
                                                lean_dec_ref(v_inst_2622_);
                                                v___x_2651_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_2630_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
                                                return v___x_2651_;
                                            } else {
                                                v___x_2652_ = lean_unsigned_to_nat(1);
                                                v___x_2653_ =
                                                    lean_nat_sub(v___x_2643_, v___x_2652_);
                                                v___x_2654_ =
                                                    lean_nat_sub(v___x_2653_, v___x_2652_);
                                                lean_dec(v___x_2653_);
                                                v___x_2655_ = l_Lean_Expr_getRevArg_x21(
                                                    v_a_2630_,
                                                    v___x_2654_,
                                                );
                                                lean_inc_ref(v_inst_2622_);
                                                v___x_2656_ = l_Lean_Meta_reduceEval___redArg(
                                                    v_inst_2622_,
                                                    v___x_2655_,
                                                    v_a_2624_,
                                                    v_a_2625_,
                                                    v_a_2626_,
                                                    v_a_2627_,
                                                );
                                                if lean_obj_tag(v___x_2656_) == 0 {
                                                    v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
                                                    lean_inc(v_a_2657_);
                                                    lean_dec_ref_known(v___x_2656_, 1);
                                                    v___x_2658_ = lean_unsigned_to_nat(2);
                                                    v___x_2659_ =
                                                        lean_nat_sub(v___x_2643_, v___x_2658_);
                                                    lean_dec(v___x_2643_);
                                                    v___x_2660_ =
                                                        lean_nat_sub(v___x_2659_, v___x_2652_);
                                                    lean_dec(v___x_2659_);
                                                    v___x_2661_ = l_Lean_Expr_getRevArg_x21(
                                                        v_a_2630_,
                                                        v___x_2660_,
                                                    );
                                                    lean_dec(v_a_2630_);
                                                    v___x_2662_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(v_inst_2622_, v___x_2661_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
                                                    if lean_obj_tag(v___x_2662_) == 0 {
                                                        v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
                                                        v_isSharedCheck_2671_ =
                                                            (!lean_is_exclusive(v___x_2662_)) as u8;
                                                        if v_isSharedCheck_2671_ == 0 {
                                                            v___x_2665_ = v___x_2662_;
                                                            v_isShared_2666_ =
                                                                v_isSharedCheck_2671_;
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_2663_);
                                                            lean_dec(v___x_2662_);
                                                            v___x_2665_ = lean_box(0);
                                                            v_isShared_2666_ =
                                                                v_isSharedCheck_2671_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec(v_a_2657_);
                                                        return v___x_2662_;
                                                    }
                                                } else {
                                                    lean_dec(v___x_2643_);
                                                    lean_dec(v_a_2630_);
                                                    lean_dec_ref(v_inst_2622_);
                                                    v_a_2672_ = lean_ctor_get(v___x_2656_, 0);
                                                    v_isSharedCheck_2679_ =
                                                        (!lean_is_exclusive(v___x_2656_)) as u8;
                                                    if v_isSharedCheck_2679_ == 0 {
                                                        v___x_2674_ = v___x_2656_;
                                                        v_isShared_2675_ = v_isSharedCheck_2679_;
                                                        state = 4;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_2672_);
                                                        lean_dec(v___x_2656_);
                                                        v___x_2674_ = lean_box(0);
                                                        v_isShared_2675_ = v_isSharedCheck_2679_;
                                                        state = 4;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v_str_2638_);
                                        lean_dec_ref(v_inst_2622_);
                                        v___x_2680_ = lean_unsigned_to_nat(1);
                                        v___x_2681_ = lean_nat_dec_eq(v___x_2643_, v___x_2680_);
                                        lean_dec(v___x_2643_);
                                        if v___x_2681_ == 0 {
                                            lean_del_object(v___x_2632_);
                                            v___x_2682_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_2630_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
                                            return v___x_2682_;
                                        } else {
                                            lean_dec(v_a_2630_);
                                            v___x_2683_ = lean_box(0);
                                            if v_isShared_2633_ == 0 {
                                                lean_ctor_set(v___x_2632_, 0, v___x_2683_);
                                                v___x_2685_ = v___x_2632_;
                                                state = 6;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_2686_ =
                                                    lean_alloc_ctor(0, 1, (0) as u32);
                                                lean_ctor_set(
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
                                lean_dec_ref_known(v_pre_2636_, 2);
                                lean_dec_ref_known(v_declName_2635_, 2);
                                lean_del_object(v___x_2632_);
                                lean_dec_ref(v_inst_2622_);
                                v___x_2687_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_2630_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
                                return v___x_2687_;
                            }
                        } else {
                            lean_dec(v_pre_2636_);
                            lean_dec_ref_known(v_declName_2635_, 2);
                            lean_del_object(v___x_2632_);
                            lean_dec_ref(v_inst_2622_);
                            v___x_2688_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_2630_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
                            return v___x_2688_;
                        }
                    } else {
                        lean_dec(v_declName_2635_);
                        lean_del_object(v___x_2632_);
                        lean_dec_ref(v_inst_2622_);
                        v___x_2689_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_2630_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
                        return v___x_2689_;
                    }
                } else {
                    lean_dec_ref(v___x_2634_);
                    lean_del_object(v___x_2632_);
                    lean_dec_ref(v_inst_2622_);
                    v___x_2690_ =
                        l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(
                            v_a_2630_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_,
                        );
                    return v___x_2690_;
                }
            }
            2 => {
                v___x_2667_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2667_, 0, v_a_2657_);
                lean_ctor_set(v___x_2667_, 1, v_a_2663_);
                if v_isShared_2666_ == 0 {
                    lean_ctor_set(v___x_2665_, 0, v___x_2667_);
                    v___x_2669_ = v___x_2665_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2667_);
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
                    v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
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
                    v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
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
    mut v_inst_2700_: *mut LeanObject,
    mut v_e_2701_: *mut LeanObject,
    mut v_a_2702_: *mut LeanObject,
    mut v_a_2703_: *mut LeanObject,
    mut v_a_2704_: *mut LeanObject,
    mut v_a_2705_: *mut LeanObject,
    mut v_a_2706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2707_: *mut LeanObject = core::ptr::null_mut();
    v_res_2707_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList___redArg(
        v_inst_2700_,
        v_e_2701_,
        v_a_2702_,
        v_a_2703_,
        v_a_2704_,
        v_a_2705_,
    );
    lean_dec(v_a_2705_);
    lean_dec_ref(v_a_2704_);
    lean_dec(v_a_2703_);
    lean_dec_ref(v_a_2702_);
    return v_res_2707_;
}
pub unsafe fn l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList(
    mut v_00_u03b1_2708_: *mut LeanObject,
    mut v_inst_2709_: *mut LeanObject,
    mut v_e_2710_: *mut LeanObject,
    mut v_a_2711_: *mut LeanObject,
    mut v_a_2712_: *mut LeanObject,
    mut v_a_2713_: *mut LeanObject,
    mut v_a_2714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2717_: *mut LeanObject,
    mut v_inst_2718_: *mut LeanObject,
    mut v_e_2719_: *mut LeanObject,
    mut v_a_2720_: *mut LeanObject,
    mut v_a_2721_: *mut LeanObject,
    mut v_a_2722_: *mut LeanObject,
    mut v_a_2723_: *mut LeanObject,
    mut v_a_2724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2725_: *mut LeanObject = core::ptr::null_mut();
    v_res_2725_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalList(
        v_00_u03b1_2717_,
        v_inst_2718_,
        v_e_2719_,
        v_a_2720_,
        v_a_2721_,
        v_a_2722_,
        v_a_2723_,
    );
    lean_dec(v_a_2723_);
    lean_dec_ref(v_a_2722_);
    lean_dec(v_a_2721_);
    lean_dec_ref(v_a_2720_);
    return v_res_2725_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalList___private__1___redArg(
    mut v_inst_2726_: *mut LeanObject,
    mut v_e_2727_: *mut LeanObject,
    mut v_a_2728_: *mut LeanObject,
    mut v_a_2729_: *mut LeanObject,
    mut v_a_2730_: *mut LeanObject,
    mut v_a_2731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_2734_: *mut LeanObject,
    mut v_e_2735_: *mut LeanObject,
    mut v_a_2736_: *mut LeanObject,
    mut v_a_2737_: *mut LeanObject,
    mut v_a_2738_: *mut LeanObject,
    mut v_a_2739_: *mut LeanObject,
    mut v_a_2740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2741_: *mut LeanObject = core::ptr::null_mut();
    v_res_2741_ = l_Lean_Meta_instReduceEvalList___private__1___redArg(
        v_inst_2734_,
        v_e_2735_,
        v_a_2736_,
        v_a_2737_,
        v_a_2738_,
        v_a_2739_,
    );
    lean_dec(v_a_2739_);
    lean_dec_ref(v_a_2738_);
    lean_dec(v_a_2737_);
    lean_dec_ref(v_a_2736_);
    return v_res_2741_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalList___private__1(
    mut v_00_u03b1_2742_: *mut LeanObject,
    mut v_inst_2743_: *mut LeanObject,
    mut v_e_2744_: *mut LeanObject,
    mut v_a_2745_: *mut LeanObject,
    mut v_a_2746_: *mut LeanObject,
    mut v_a_2747_: *mut LeanObject,
    mut v_a_2748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2751_: *mut LeanObject,
    mut v_inst_2752_: *mut LeanObject,
    mut v_e_2753_: *mut LeanObject,
    mut v_a_2754_: *mut LeanObject,
    mut v_a_2755_: *mut LeanObject,
    mut v_a_2756_: *mut LeanObject,
    mut v_a_2757_: *mut LeanObject,
    mut v_a_2758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2759_: *mut LeanObject = core::ptr::null_mut();
    v_res_2759_ = l_Lean_Meta_instReduceEvalList___private__1(
        v_00_u03b1_2751_,
        v_inst_2752_,
        v_e_2753_,
        v_a_2754_,
        v_a_2755_,
        v_a_2756_,
        v_a_2757_,
    );
    lean_dec(v_a_2757_);
    lean_dec_ref(v_a_2756_);
    lean_dec(v_a_2755_);
    lean_dec_ref(v_a_2754_);
    return v_res_2759_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalList___redArg(
    mut v_inst_2760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    v___x_2761_ = lean_alloc_closure(
        l_Lean_Meta_instReduceEvalList___private__1___boxed as *mut core::ffi::c_void,
        8,
        2,
    );
    lean_closure_set(v___x_2761_, 0, lean_box(0));
    lean_closure_set(v___x_2761_, 1, v_inst_2760_);
    return v___x_2761_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalList(
    mut v_00_u03b1_2762_: *mut LeanObject,
    mut v_inst_2763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    v___x_2764_ = lean_alloc_closure(
        l_Lean_Meta_instReduceEvalList___private__1___boxed as *mut core::ffi::c_void,
        8,
        2,
    );
    lean_closure_set(v___x_2764_, 0, lean_box(0));
    lean_closure_set(v___x_2764_, 1, v_inst_2763_);
    return v___x_2764_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg(
    mut v_n_2770_: *mut LeanObject,
    mut v_e_2771_: *mut LeanObject,
    mut v_a_2772_: *mut LeanObject,
    mut v_a_2773_: *mut LeanObject,
    mut v_a_2774_: *mut LeanObject,
    mut v_a_2775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: u8 = 0;
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2793_: u8 = 0;
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2798_: u8 = 0;
    let mut v_a_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2802_: u8 = 0;
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2806_: u8 = 0;
    let mut v_a_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2810_: u8 = 0;
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2814_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_2775_);
                lean_inc_ref(v_a_2774_);
                lean_inc(v_a_2773_);
                lean_inc_ref(v_a_2772_);
                v___x_2777_ = lean_whnf(v_e_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_);
                if lean_obj_tag(v___x_2777_) == 0 {
                    v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
                    lean_inc(v_a_2778_);
                    lean_dec_ref_known(v___x_2777_, 1);
                    v___x_2779_ =
                        l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2;
                    v___x_2780_ = lean_unsigned_to_nat(3);
                    v___x_2781_ = l_Lean_Expr_isAppOfArity(v_a_2778_, v___x_2779_, v___x_2780_);
                    if v___x_2781_ == 0 {
                        v___x_2782_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_2778_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_);
                        return v___x_2782_;
                    } else {
                        v___f_2783_ = l_Lean_Meta_instReduceEvalNat___closed__0;
                        v___x_2784_ = lean_unsigned_to_nat(1);
                        v___x_2785_ = l_Lean_Expr_getAppNumArgs(v_a_2778_);
                        v___x_2786_ = lean_nat_sub(v___x_2785_, v___x_2784_);
                        lean_dec(v___x_2785_);
                        v___x_2787_ = lean_nat_sub(v___x_2786_, v___x_2784_);
                        lean_dec(v___x_2786_);
                        v___x_2788_ = l_Lean_Expr_getRevArg_x21(v_a_2778_, v___x_2787_);
                        lean_dec(v_a_2778_);
                        v___x_2789_ = l_Lean_Meta_reduceEval___redArg(
                            v___f_2783_,
                            v___x_2788_,
                            v_a_2772_,
                            v_a_2773_,
                            v_a_2774_,
                            v_a_2775_,
                        );
                        if lean_obj_tag(v___x_2789_) == 0 {
                            v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
                            v_isSharedCheck_2798_ = (!lean_is_exclusive(v___x_2789_)) as u8;
                            if v_isSharedCheck_2798_ == 0 {
                                v___x_2792_ = v___x_2789_;
                                v_isShared_2793_ = v_isSharedCheck_2798_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2790_);
                                lean_dec(v___x_2789_);
                                v___x_2792_ = lean_box(0);
                                v_isShared_2793_ = v_isSharedCheck_2798_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_2799_ = lean_ctor_get(v___x_2789_, 0);
                            v_isSharedCheck_2806_ = (!lean_is_exclusive(v___x_2789_)) as u8;
                            if v_isSharedCheck_2806_ == 0 {
                                v___x_2801_ = v___x_2789_;
                                v_isShared_2802_ = v_isSharedCheck_2806_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_2799_);
                                lean_dec(v___x_2789_);
                                v___x_2801_ = lean_box(0);
                                v_isShared_2802_ = v_isSharedCheck_2806_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_2807_ = lean_ctor_get(v___x_2777_, 0);
                    v_isSharedCheck_2814_ = (!lean_is_exclusive(v___x_2777_)) as u8;
                    if v_isSharedCheck_2814_ == 0 {
                        v___x_2809_ = v___x_2777_;
                        v_isShared_2810_ = v_isSharedCheck_2814_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2807_);
                        lean_dec(v___x_2777_);
                        v___x_2809_ = lean_box(0);
                        v_isShared_2810_ = v_isSharedCheck_2814_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2794_ = lean_nat_mod(v_a_2790_, v_n_2770_);
                lean_dec(v_a_2790_);
                if v_isShared_2793_ == 0 {
                    lean_ctor_set(v___x_2792_, 0, v___x_2794_);
                    v___x_2796_ = v___x_2792_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
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
                    v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
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
                    v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
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
    mut v_n_2815_: *mut LeanObject,
    mut v_e_2816_: *mut LeanObject,
    mut v_a_2817_: *mut LeanObject,
    mut v_a_2818_: *mut LeanObject,
    mut v_a_2819_: *mut LeanObject,
    mut v_a_2820_: *mut LeanObject,
    mut v_a_2821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2822_: *mut LeanObject = core::ptr::null_mut();
    v_res_2822_ = l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg(
        v_n_2815_, v_e_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_,
    );
    lean_dec(v_a_2820_);
    lean_dec_ref(v_a_2819_);
    lean_dec(v_a_2818_);
    lean_dec_ref(v_a_2817_);
    lean_dec(v_n_2815_);
    return v_res_2822_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1(
    mut v_n_2823_: *mut LeanObject,
    mut v_inst_2824_: *mut LeanObject,
    mut v_e_2825_: *mut LeanObject,
    mut v_a_2826_: *mut LeanObject,
    mut v_a_2827_: *mut LeanObject,
    mut v_a_2828_: *mut LeanObject,
    mut v_a_2829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: u8 = 0;
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2847_: u8 = 0;
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2852_: u8 = 0;
    let mut v_a_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2856_: u8 = 0;
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2860_: u8 = 0;
    let mut v_a_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2864_: u8 = 0;
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2868_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_2829_);
                lean_inc_ref(v_a_2828_);
                lean_inc(v_a_2827_);
                lean_inc_ref(v_a_2826_);
                v___x_2831_ = lean_whnf(v_e_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_);
                if lean_obj_tag(v___x_2831_) == 0 {
                    v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
                    lean_inc(v_a_2832_);
                    lean_dec_ref_known(v___x_2831_, 1);
                    v___x_2833_ =
                        l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___redArg___closed__2;
                    v___x_2834_ = lean_unsigned_to_nat(3);
                    v___x_2835_ = l_Lean_Expr_isAppOfArity(v_a_2832_, v___x_2833_, v___x_2834_);
                    if v___x_2835_ == 0 {
                        v___x_2836_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_2832_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_);
                        return v___x_2836_;
                    } else {
                        v___f_2837_ = l_Lean_Meta_instReduceEvalNat___closed__0;
                        v___x_2838_ = lean_unsigned_to_nat(1);
                        v___x_2839_ = l_Lean_Expr_getAppNumArgs(v_a_2832_);
                        v___x_2840_ = lean_nat_sub(v___x_2839_, v___x_2838_);
                        lean_dec(v___x_2839_);
                        v___x_2841_ = lean_nat_sub(v___x_2840_, v___x_2838_);
                        lean_dec(v___x_2840_);
                        v___x_2842_ = l_Lean_Expr_getRevArg_x21(v_a_2832_, v___x_2841_);
                        lean_dec(v_a_2832_);
                        v___x_2843_ = l_Lean_Meta_reduceEval___redArg(
                            v___f_2837_,
                            v___x_2842_,
                            v_a_2826_,
                            v_a_2827_,
                            v_a_2828_,
                            v_a_2829_,
                        );
                        if lean_obj_tag(v___x_2843_) == 0 {
                            v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
                            v_isSharedCheck_2852_ = (!lean_is_exclusive(v___x_2843_)) as u8;
                            if v_isSharedCheck_2852_ == 0 {
                                v___x_2846_ = v___x_2843_;
                                v_isShared_2847_ = v_isSharedCheck_2852_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2844_);
                                lean_dec(v___x_2843_);
                                v___x_2846_ = lean_box(0);
                                v_isShared_2847_ = v_isSharedCheck_2852_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_2853_ = lean_ctor_get(v___x_2843_, 0);
                            v_isSharedCheck_2860_ = (!lean_is_exclusive(v___x_2843_)) as u8;
                            if v_isSharedCheck_2860_ == 0 {
                                v___x_2855_ = v___x_2843_;
                                v_isShared_2856_ = v_isSharedCheck_2860_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_2853_);
                                lean_dec(v___x_2843_);
                                v___x_2855_ = lean_box(0);
                                v_isShared_2856_ = v_isSharedCheck_2860_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_2861_ = lean_ctor_get(v___x_2831_, 0);
                    v_isSharedCheck_2868_ = (!lean_is_exclusive(v___x_2831_)) as u8;
                    if v_isSharedCheck_2868_ == 0 {
                        v___x_2863_ = v___x_2831_;
                        v_isShared_2864_ = v_isSharedCheck_2868_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2861_);
                        lean_dec(v___x_2831_);
                        v___x_2863_ = lean_box(0);
                        v_isShared_2864_ = v_isSharedCheck_2868_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2848_ = lean_nat_mod(v_a_2844_, v_n_2823_);
                lean_dec(v_a_2844_);
                if v_isShared_2847_ == 0 {
                    lean_ctor_set(v___x_2846_, 0, v___x_2848_);
                    v___x_2850_ = v___x_2846_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2848_);
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
                    v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
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
                    v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
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
    mut v_n_2869_: *mut LeanObject,
    mut v_inst_2870_: *mut LeanObject,
    mut v_e_2871_: *mut LeanObject,
    mut v_a_2872_: *mut LeanObject,
    mut v_a_2873_: *mut LeanObject,
    mut v_a_2874_: *mut LeanObject,
    mut v_a_2875_: *mut LeanObject,
    mut v_a_2876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2877_: *mut LeanObject = core::ptr::null_mut();
    v_res_2877_ = l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1(
        v_n_2869_,
        v_inst_2870_,
        v_e_2871_,
        v_a_2872_,
        v_a_2873_,
        v_a_2874_,
        v_a_2875_,
    );
    lean_dec(v_a_2875_);
    lean_dec_ref(v_a_2874_);
    lean_dec(v_a_2873_);
    lean_dec_ref(v_a_2872_);
    lean_dec(v_n_2869_);
    return v_res_2877_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalFinOfNeZeroNat___redArg(
    mut v_n_2878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    v___x_2879_ = lean_alloc_closure(
        l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed as *mut core::ffi::c_void,
        8,
        2,
    );
    lean_closure_set(v___x_2879_, 0, v_n_2878_);
    lean_closure_set(v___x_2879_, 1, lean_box(0));
    return v___x_2879_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalFinOfNeZeroNat(
    mut v_n_2880_: *mut LeanObject,
    mut v_inst_2881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    v___x_2882_ = lean_alloc_closure(
        l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed as *mut core::ffi::c_void,
        8,
        2,
    );
    lean_closure_set(v___x_2882_, 0, v_n_2880_);
    lean_closure_set(v___x_2882_, 1, lean_box(0));
    return v___x_2882_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalBitVec___private__1(
    mut v_n_2888_: *mut LeanObject,
    mut v_e_2889_: *mut LeanObject,
    mut v_a_2890_: *mut LeanObject,
    mut v_a_2891_: *mut LeanObject,
    mut v_a_2892_: *mut LeanObject,
    mut v_a_2893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: u8 = 0;
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2914_: u8 = 0;
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2918_: u8 = 0;
    let mut v_a_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2922_: u8 = 0;
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2926_: u8 = 0;
    let mut v_a_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2930_: u8 = 0;
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_2893_);
                lean_inc_ref(v_a_2892_);
                lean_inc(v_a_2891_);
                lean_inc_ref(v_a_2890_);
                v___x_2895_ = lean_whnf(v_e_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
                if lean_obj_tag(v___x_2895_) == 0 {
                    v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
                    lean_inc(v_a_2896_);
                    lean_dec_ref_known(v___x_2895_, 1);
                    v___x_2897_ = l_Lean_Meta_instReduceEvalBitVec___private__1___closed__2;
                    v___x_2898_ = lean_unsigned_to_nat(2);
                    v___x_2899_ = l_Lean_Expr_isAppOfArity(v_a_2896_, v___x_2897_, v___x_2898_);
                    if v___x_2899_ == 0 {
                        v___x_2900_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_2896_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
                        return v___x_2900_;
                    } else {
                        v___x_2901_ = lean_nat_pow(v___x_2898_, v_n_2888_);
                        v___x_2902_ = lean_unsigned_to_nat(1);
                        v___x_2903_ = lean_nat_sub(v___x_2901_, v___x_2902_);
                        lean_dec(v___x_2901_);
                        v___x_2904_ = lean_nat_add(v___x_2903_, v___x_2902_);
                        lean_dec(v___x_2903_);
                        v___x_2905_ = lean_alloc_closure(
                            l_Lean_Meta_instReduceEvalFinOfNeZeroNat___private__1___boxed
                                as *mut core::ffi::c_void,
                            8,
                            2,
                        );
                        lean_closure_set(v___x_2905_, 0, v___x_2904_);
                        lean_closure_set(v___x_2905_, 1, lean_box(0));
                        v___x_2906_ = l_Lean_Expr_getAppNumArgs(v_a_2896_);
                        v___x_2907_ = lean_nat_sub(v___x_2906_, v___x_2902_);
                        lean_dec(v___x_2906_);
                        v___x_2908_ = lean_nat_sub(v___x_2907_, v___x_2902_);
                        lean_dec(v___x_2907_);
                        v___x_2909_ = l_Lean_Expr_getRevArg_x21(v_a_2896_, v___x_2908_);
                        lean_dec(v_a_2896_);
                        v___x_2910_ = l_Lean_Meta_reduceEval___redArg(
                            v___x_2905_,
                            v___x_2909_,
                            v_a_2890_,
                            v_a_2891_,
                            v_a_2892_,
                            v_a_2893_,
                        );
                        if lean_obj_tag(v___x_2910_) == 0 {
                            v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
                            v_isSharedCheck_2918_ = (!lean_is_exclusive(v___x_2910_)) as u8;
                            if v_isSharedCheck_2918_ == 0 {
                                v___x_2913_ = v___x_2910_;
                                v_isShared_2914_ = v_isSharedCheck_2918_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2911_);
                                lean_dec(v___x_2910_);
                                v___x_2913_ = lean_box(0);
                                v_isShared_2914_ = v_isSharedCheck_2918_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_2919_ = lean_ctor_get(v___x_2910_, 0);
                            v_isSharedCheck_2926_ = (!lean_is_exclusive(v___x_2910_)) as u8;
                            if v_isSharedCheck_2926_ == 0 {
                                v___x_2921_ = v___x_2910_;
                                v_isShared_2922_ = v_isSharedCheck_2926_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_2919_);
                                lean_dec(v___x_2910_);
                                v___x_2921_ = lean_box(0);
                                v_isShared_2922_ = v_isSharedCheck_2926_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_2927_ = lean_ctor_get(v___x_2895_, 0);
                    v_isSharedCheck_2934_ = (!lean_is_exclusive(v___x_2895_)) as u8;
                    if v_isSharedCheck_2934_ == 0 {
                        v___x_2929_ = v___x_2895_;
                        v_isShared_2930_ = v_isSharedCheck_2934_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2927_);
                        lean_dec(v___x_2895_);
                        v___x_2929_ = lean_box(0);
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
                    v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
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
                    v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
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
                    v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
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
    mut v_n_2935_: *mut LeanObject,
    mut v_e_2936_: *mut LeanObject,
    mut v_a_2937_: *mut LeanObject,
    mut v_a_2938_: *mut LeanObject,
    mut v_a_2939_: *mut LeanObject,
    mut v_a_2940_: *mut LeanObject,
    mut v_a_2941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2942_: *mut LeanObject = core::ptr::null_mut();
    v_res_2942_ = l_Lean_Meta_instReduceEvalBitVec___private__1(
        v_n_2935_, v_e_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_,
    );
    lean_dec(v_a_2940_);
    lean_dec_ref(v_a_2939_);
    lean_dec(v_a_2938_);
    lean_dec_ref(v_a_2937_);
    lean_dec(v_n_2935_);
    return v_res_2942_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalBitVec(mut v_n_2943_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    v___x_2944_ = lean_alloc_closure(
        l_Lean_Meta_instReduceEvalBitVec___private__1___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___x_2944_, 0, v_n_2943_);
    return v___x_2944_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalBool___private__1(
    mut v_e_2954_: *mut LeanObject,
    mut v_a_2955_: *mut LeanObject,
    mut v_a_2956_: *mut LeanObject,
    mut v_a_2957_: *mut LeanObject,
    mut v_a_2958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2964_: u8 = 0;
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: u8 = 0;
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: u8 = 0;
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2978_: u8 = 0;
    let mut v_a_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2982_: u8 = 0;
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_2958_);
                lean_inc_ref(v_a_2957_);
                lean_inc(v_a_2956_);
                lean_inc_ref(v_a_2955_);
                v___x_2960_ = lean_whnf(v_e_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_);
                if lean_obj_tag(v___x_2960_) == 0 {
                    v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
                    v_isSharedCheck_2978_ = (!lean_is_exclusive(v___x_2960_)) as u8;
                    if v_isSharedCheck_2978_ == 0 {
                        v___x_2963_ = v___x_2960_;
                        v_isShared_2964_ = v_isSharedCheck_2978_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2961_);
                        lean_dec(v___x_2960_);
                        v___x_2963_ = lean_box(0);
                        v_isShared_2964_ = v_isSharedCheck_2978_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2979_ = lean_ctor_get(v___x_2960_, 0);
                    v_isSharedCheck_2986_ = (!lean_is_exclusive(v___x_2960_)) as u8;
                    if v_isSharedCheck_2986_ == 0 {
                        v___x_2981_ = v___x_2960_;
                        v_isShared_2982_ = v_isSharedCheck_2986_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2979_);
                        lean_dec(v___x_2960_);
                        v___x_2981_ = lean_box(0);
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
                        lean_del_object(v___x_2963_);
                        v___x_2969_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_2961_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_);
                        return v___x_2969_;
                    } else {
                        lean_dec(v_a_2961_);
                        v___x_2970_ = lean_box((v___x_2966_) as usize);
                        if v_isShared_2964_ == 0 {
                            lean_ctor_set(v___x_2963_, 0, v___x_2970_);
                            v___x_2972_ = v___x_2963_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2970_);
                            v___x_2972_ = v_reuseFailAlloc_2973_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_2961_);
                    v___x_2974_ = lean_box((v___x_2966_) as usize);
                    if v_isShared_2964_ == 0 {
                        lean_ctor_set(v___x_2963_, 0, v___x_2974_);
                        v___x_2976_ = v___x_2963_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2974_);
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
                    v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
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
    mut v_e_2987_: *mut LeanObject,
    mut v_a_2988_: *mut LeanObject,
    mut v_a_2989_: *mut LeanObject,
    mut v_a_2990_: *mut LeanObject,
    mut v_a_2991_: *mut LeanObject,
    mut v_a_2992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2993_: *mut LeanObject = core::ptr::null_mut();
    v_res_2993_ = l_Lean_Meta_instReduceEvalBool___private__1(
        v_e_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_,
    );
    lean_dec(v_a_2991_);
    lean_dec_ref(v_a_2990_);
    lean_dec(v_a_2989_);
    lean_dec_ref(v_a_2988_);
    return v_res_2993_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalBinderInfo___private__1(
    mut v_e_3001_: *mut LeanObject,
    mut v_a_3002_: *mut LeanObject,
    mut v_a_3003_: *mut LeanObject,
    mut v_a_3004_: *mut LeanObject,
    mut v_a_3005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3011_: u8 = 0;
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: u8 = 0;
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: u8 = 0;
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: u8 = 0;
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: u8 = 0;
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: u8 = 0;
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: u8 = 0;
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: u8 = 0;
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: u8 = 0;
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: u8 = 0;
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: u8 = 0;
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3060_: u8 = 0;
    let mut v_a_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3064_: u8 = 0;
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_3005_);
                lean_inc_ref(v_a_3004_);
                lean_inc(v_a_3003_);
                lean_inc_ref(v_a_3002_);
                lean_inc_ref(v_e_3001_);
                v___x_3007_ = lean_whnf(v_e_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
                if lean_obj_tag(v___x_3007_) == 0 {
                    v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
                    v_isSharedCheck_3060_ = (!lean_is_exclusive(v___x_3007_)) as u8;
                    if v_isSharedCheck_3060_ == 0 {
                        v___x_3010_ = v___x_3007_;
                        v_isShared_3011_ = v_isSharedCheck_3060_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3008_);
                        lean_dec(v___x_3007_);
                        v___x_3010_ = lean_box(0);
                        v_isShared_3011_ = v_isSharedCheck_3060_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_3001_);
                    v_a_3061_ = lean_ctor_get(v___x_3007_, 0);
                    v_isSharedCheck_3068_ = (!lean_is_exclusive(v___x_3007_)) as u8;
                    if v_isSharedCheck_3068_ == 0 {
                        v___x_3063_ = v___x_3007_;
                        v_isShared_3064_ = v_isSharedCheck_3068_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3061_);
                        lean_dec(v___x_3007_);
                        v___x_3063_ = lean_box(0);
                        v_isShared_3064_ = v_isSharedCheck_3068_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3012_ = l_Lean_Expr_constName_x3f(v_a_3008_);
                lean_dec(v_a_3008_);
                if lean_obj_tag(v___x_3012_) == 1 {
                    v_val_3013_ = lean_ctor_get(v___x_3012_, 0);
                    lean_inc(v_val_3013_);
                    lean_dec_ref_known(v___x_3012_, 1);
                    if lean_obj_tag(v_val_3013_) == 1 {
                        v_pre_3014_ = lean_ctor_get(v_val_3013_, 0);
                        lean_inc(v_pre_3014_);
                        if lean_obj_tag(v_pre_3014_) == 1 {
                            v_pre_3015_ = lean_ctor_get(v_pre_3014_, 0);
                            lean_inc(v_pre_3015_);
                            if lean_obj_tag(v_pre_3015_) == 1 {
                                v_pre_3016_ = lean_ctor_get(v_pre_3015_, 0);
                                if lean_obj_tag(v_pre_3016_) == 0 {
                                    v_str_3017_ = lean_ctor_get(v_val_3013_, 1);
                                    lean_inc_ref(v_str_3017_);
                                    lean_dec_ref_known(v_val_3013_, 2);
                                    v_str_3018_ = lean_ctor_get(v_pre_3014_, 1);
                                    lean_inc_ref(v_str_3018_);
                                    lean_dec_ref_known(v_pre_3014_, 2);
                                    v_str_3019_ = lean_ctor_get(v_pre_3015_, 1);
                                    lean_inc_ref(v_str_3019_);
                                    lean_dec_ref_known(v_pre_3015_, 2);
                                    v___x_3020_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__0;
                                    v___x_3021_ = lean_string_dec_eq(v_str_3019_, v___x_3020_);
                                    lean_dec_ref(v_str_3019_);
                                    if v___x_3021_ == 0 {
                                        lean_dec_ref(v_str_3018_);
                                        lean_dec_ref(v_str_3017_);
                                        lean_del_object(v___x_3010_);
                                        v___x_3022_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
                                        return v___x_3022_;
                                    } else {
                                        v___x_3023_ = l_Lean_Meta_instReduceEvalBinderInfo___private__1___closed__0;
                                        v___x_3024_ = lean_string_dec_eq(v_str_3018_, v___x_3023_);
                                        lean_dec_ref(v_str_3018_);
                                        if v___x_3024_ == 0 {
                                            lean_dec_ref(v_str_3017_);
                                            lean_del_object(v___x_3010_);
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
                                                        lean_dec_ref(v_str_3017_);
                                                        if v___x_3033_ == 0 {
                                                            lean_del_object(v___x_3010_);
                                                            v___x_3034_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
                                                            return v___x_3034_;
                                                        } else {
                                                            lean_dec_ref(v_e_3001_);
                                                            v___x_3035_ = 3;
                                                            v___x_3036_ =
                                                                lean_box((v___x_3035_) as usize);
                                                            if v_isShared_3011_ == 0 {
                                                                lean_ctor_set(
                                                                    v___x_3010_,
                                                                    0,
                                                                    v___x_3036_,
                                                                );
                                                                v___x_3038_ = v___x_3010_;
                                                                state = 2;
                                                                continue;
                                                            } else {
                                                                v_reuseFailAlloc_3039_ =
                                                                    lean_alloc_ctor(
                                                                        0,
                                                                        1,
                                                                        (0) as u32,
                                                                    );
                                                                lean_ctor_set(
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
                                                        lean_dec_ref(v_str_3017_);
                                                        lean_dec_ref(v_e_3001_);
                                                        v___x_3040_ = 2;
                                                        v___x_3041_ =
                                                            lean_box((v___x_3040_) as usize);
                                                        if v_isShared_3011_ == 0 {
                                                            lean_ctor_set(
                                                                v___x_3010_,
                                                                0,
                                                                v___x_3041_,
                                                            );
                                                            v___x_3043_ = v___x_3010_;
                                                            state = 3;
                                                            continue;
                                                        } else {
                                                            v_reuseFailAlloc_3044_ =
                                                                lean_alloc_ctor(0, 1, (0) as u32);
                                                            lean_ctor_set(
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
                                                    lean_dec_ref(v_str_3017_);
                                                    lean_dec_ref(v_e_3001_);
                                                    v___x_3045_ = 1;
                                                    v___x_3046_ = lean_box((v___x_3045_) as usize);
                                                    if v_isShared_3011_ == 0 {
                                                        lean_ctor_set(v___x_3010_, 0, v___x_3046_);
                                                        v___x_3048_ = v___x_3010_;
                                                        state = 4;
                                                        continue;
                                                    } else {
                                                        v_reuseFailAlloc_3049_ =
                                                            lean_alloc_ctor(0, 1, (0) as u32);
                                                        lean_ctor_set(
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
                                                lean_dec_ref(v_str_3017_);
                                                lean_dec_ref(v_e_3001_);
                                                v___x_3050_ = 0;
                                                v___x_3051_ = lean_box((v___x_3050_) as usize);
                                                if v_isShared_3011_ == 0 {
                                                    lean_ctor_set(v___x_3010_, 0, v___x_3051_);
                                                    v___x_3053_ = v___x_3010_;
                                                    state = 5;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_3054_ =
                                                        lean_alloc_ctor(0, 1, (0) as u32);
                                                    lean_ctor_set(
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
                                    lean_dec_ref_known(v_pre_3015_, 2);
                                    lean_dec_ref_known(v_pre_3014_, 2);
                                    lean_dec_ref_known(v_val_3013_, 2);
                                    lean_del_object(v___x_3010_);
                                    v___x_3055_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
                                    return v___x_3055_;
                                }
                            } else {
                                lean_dec_ref_known(v_pre_3014_, 2);
                                lean_dec(v_pre_3015_);
                                lean_dec_ref_known(v_val_3013_, 2);
                                lean_del_object(v___x_3010_);
                                v___x_3056_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
                                return v___x_3056_;
                            }
                        } else {
                            lean_dec(v_pre_3014_);
                            lean_dec_ref_known(v_val_3013_, 2);
                            lean_del_object(v___x_3010_);
                            v___x_3057_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
                            return v___x_3057_;
                        }
                    } else {
                        lean_dec(v_val_3013_);
                        lean_del_object(v___x_3010_);
                        v___x_3058_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_e_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
                        return v___x_3058_;
                    }
                } else {
                    lean_dec(v___x_3012_);
                    lean_del_object(v___x_3010_);
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
                    v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
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
    mut v_e_3069_: *mut LeanObject,
    mut v_a_3070_: *mut LeanObject,
    mut v_a_3071_: *mut LeanObject,
    mut v_a_3072_: *mut LeanObject,
    mut v_a_3073_: *mut LeanObject,
    mut v_a_3074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3075_: *mut LeanObject = core::ptr::null_mut();
    v_res_3075_ = l_Lean_Meta_instReduceEvalBinderInfo___private__1(
        v_e_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_,
    );
    lean_dec(v_a_3073_);
    lean_dec_ref(v_a_3072_);
    lean_dec(v_a_3071_);
    lean_dec_ref(v_a_3070_);
    return v_res_3075_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalLiteral___private__1(
    mut v_e_3089_: *mut LeanObject,
    mut v_a_3090_: *mut LeanObject,
    mut v_a_3091_: *mut LeanObject,
    mut v_a_3092_: *mut LeanObject,
    mut v_a_3093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: u8 = 0;
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: u8 = 0;
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3111_: u8 = 0;
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3116_: u8 = 0;
    let mut v_a_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3120_: u8 = 0;
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3124_: u8 = 0;
    let mut v___f_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3133_: u8 = 0;
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3138_: u8 = 0;
    let mut v_a_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3142_: u8 = 0;
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3146_: u8 = 0;
    let mut v_a_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3150_: u8 = 0;
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3154_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_3093_);
                lean_inc_ref(v_a_3092_);
                lean_inc(v_a_3091_);
                lean_inc_ref(v_a_3090_);
                v___x_3095_ = lean_whnf(v_e_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
                if lean_obj_tag(v___x_3095_) == 0 {
                    v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
                    lean_inc(v_a_3096_);
                    lean_dec_ref_known(v___x_3095_, 1);
                    v___x_3097_ = l_Lean_Meta_instReduceEvalLiteral___private__1___closed__2;
                    v___x_3098_ = lean_unsigned_to_nat(1);
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
                            lean_dec(v___x_3104_);
                            v___x_3106_ = l_Lean_Expr_getRevArg_x21(v_a_3096_, v___x_3105_);
                            lean_dec(v_a_3096_);
                            v___x_3107_ = l_Lean_Meta_reduceEval___redArg(
                                v___f_3103_,
                                v___x_3106_,
                                v_a_3090_,
                                v_a_3091_,
                                v_a_3092_,
                                v_a_3093_,
                            );
                            if lean_obj_tag(v___x_3107_) == 0 {
                                v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
                                v_isSharedCheck_3116_ = (!lean_is_exclusive(v___x_3107_)) as u8;
                                if v_isSharedCheck_3116_ == 0 {
                                    v___x_3110_ = v___x_3107_;
                                    v_isShared_3111_ = v_isSharedCheck_3116_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_3108_);
                                    lean_dec(v___x_3107_);
                                    v___x_3110_ = lean_box(0);
                                    v_isShared_3111_ = v_isSharedCheck_3116_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_3117_ = lean_ctor_get(v___x_3107_, 0);
                                v_isSharedCheck_3124_ = (!lean_is_exclusive(v___x_3107_)) as u8;
                                if v_isSharedCheck_3124_ == 0 {
                                    v___x_3119_ = v___x_3107_;
                                    v_isShared_3120_ = v_isSharedCheck_3124_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_3117_);
                                    lean_dec(v___x_3107_);
                                    v___x_3119_ = lean_box(0);
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
                        lean_dec(v___x_3126_);
                        v___x_3128_ = l_Lean_Expr_getRevArg_x21(v_a_3096_, v___x_3127_);
                        lean_dec(v_a_3096_);
                        v___x_3129_ = l_Lean_Meta_reduceEval___redArg(
                            v___f_3125_,
                            v___x_3128_,
                            v_a_3090_,
                            v_a_3091_,
                            v_a_3092_,
                            v_a_3093_,
                        );
                        if lean_obj_tag(v___x_3129_) == 0 {
                            v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
                            v_isSharedCheck_3138_ = (!lean_is_exclusive(v___x_3129_)) as u8;
                            if v_isSharedCheck_3138_ == 0 {
                                v___x_3132_ = v___x_3129_;
                                v_isShared_3133_ = v_isSharedCheck_3138_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_3130_);
                                lean_dec(v___x_3129_);
                                v___x_3132_ = lean_box(0);
                                v_isShared_3133_ = v_isSharedCheck_3138_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v_a_3139_ = lean_ctor_get(v___x_3129_, 0);
                            v_isSharedCheck_3146_ = (!lean_is_exclusive(v___x_3129_)) as u8;
                            if v_isSharedCheck_3146_ == 0 {
                                v___x_3141_ = v___x_3129_;
                                v_isShared_3142_ = v_isSharedCheck_3146_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_3139_);
                                lean_dec(v___x_3129_);
                                v___x_3141_ = lean_box(0);
                                v_isShared_3142_ = v_isSharedCheck_3146_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_3147_ = lean_ctor_get(v___x_3095_, 0);
                    v_isSharedCheck_3154_ = (!lean_is_exclusive(v___x_3095_)) as u8;
                    if v_isSharedCheck_3154_ == 0 {
                        v___x_3149_ = v___x_3095_;
                        v_isShared_3150_ = v_isSharedCheck_3154_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_3147_);
                        lean_dec(v___x_3095_);
                        v___x_3149_ = lean_box(0);
                        v_isShared_3150_ = v_isSharedCheck_3154_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3112_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3112_, 0, v_a_3108_);
                if v_isShared_3111_ == 0 {
                    lean_ctor_set(v___x_3110_, 0, v___x_3112_);
                    v___x_3114_ = v___x_3110_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3112_);
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
                    v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
                    v___x_3122_ = v_reuseFailAlloc_3123_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3122_;
            }
            5 => {
                v___x_3134_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3134_, 0, v_a_3130_);
                if v_isShared_3133_ == 0 {
                    lean_ctor_set(v___x_3132_, 0, v___x_3134_);
                    v___x_3136_ = v___x_3132_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3134_);
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
                    v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
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
                    v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
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
    mut v_e_3155_: *mut LeanObject,
    mut v_a_3156_: *mut LeanObject,
    mut v_a_3157_: *mut LeanObject,
    mut v_a_3158_: *mut LeanObject,
    mut v_a_3159_: *mut LeanObject,
    mut v_a_3160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3161_: *mut LeanObject = core::ptr::null_mut();
    v_res_3161_ = l_Lean_Meta_instReduceEvalLiteral___private__1(
        v_e_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_,
    );
    lean_dec(v_a_3159_);
    lean_dec_ref(v_a_3158_);
    lean_dec(v_a_3157_);
    lean_dec_ref(v_a_3156_);
    return v_res_3161_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalMVarId___private__1(
    mut v_e_3169_: *mut LeanObject,
    mut v_a_3170_: *mut LeanObject,
    mut v_a_3171_: *mut LeanObject,
    mut v_a_3172_: *mut LeanObject,
    mut v_a_3173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: u8 = 0;
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3189_: u8 = 0;
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3193_: u8 = 0;
    let mut v_a_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3197_: u8 = 0;
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3201_: u8 = 0;
    let mut v_a_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3205_: u8 = 0;
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3209_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_3173_);
                lean_inc_ref(v_a_3172_);
                lean_inc(v_a_3171_);
                lean_inc_ref(v_a_3170_);
                v___x_3175_ = lean_whnf(v_e_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_);
                if lean_obj_tag(v___x_3175_) == 0 {
                    v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
                    lean_inc(v_a_3176_);
                    lean_dec_ref_known(v___x_3175_, 1);
                    v___x_3177_ = l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1;
                    v___x_3178_ = lean_unsigned_to_nat(1);
                    v___x_3179_ = l_Lean_Expr_isAppOfArity(v_a_3176_, v___x_3177_, v___x_3178_);
                    if v___x_3179_ == 0 {
                        v___x_3180_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_3176_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_);
                        return v___x_3180_;
                    } else {
                        v___x_3181_ = l_Lean_Meta_instReduceEvalName___closed__0;
                        v___x_3182_ = l_Lean_Expr_getAppNumArgs(v_a_3176_);
                        v___x_3183_ = lean_nat_sub(v___x_3182_, v___x_3178_);
                        lean_dec(v___x_3182_);
                        v___x_3184_ = l_Lean_Expr_getRevArg_x21(v_a_3176_, v___x_3183_);
                        lean_dec(v_a_3176_);
                        v___x_3185_ = l_Lean_Meta_reduceEval___redArg(
                            v___x_3181_,
                            v___x_3184_,
                            v_a_3170_,
                            v_a_3171_,
                            v_a_3172_,
                            v_a_3173_,
                        );
                        if lean_obj_tag(v___x_3185_) == 0 {
                            v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
                            v_isSharedCheck_3193_ = (!lean_is_exclusive(v___x_3185_)) as u8;
                            if v_isSharedCheck_3193_ == 0 {
                                v___x_3188_ = v___x_3185_;
                                v_isShared_3189_ = v_isSharedCheck_3193_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3186_);
                                lean_dec(v___x_3185_);
                                v___x_3188_ = lean_box(0);
                                v_isShared_3189_ = v_isSharedCheck_3193_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_3194_ = lean_ctor_get(v___x_3185_, 0);
                            v_isSharedCheck_3201_ = (!lean_is_exclusive(v___x_3185_)) as u8;
                            if v_isSharedCheck_3201_ == 0 {
                                v___x_3196_ = v___x_3185_;
                                v_isShared_3197_ = v_isSharedCheck_3201_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_3194_);
                                lean_dec(v___x_3185_);
                                v___x_3196_ = lean_box(0);
                                v_isShared_3197_ = v_isSharedCheck_3201_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_3202_ = lean_ctor_get(v___x_3175_, 0);
                    v_isSharedCheck_3209_ = (!lean_is_exclusive(v___x_3175_)) as u8;
                    if v_isSharedCheck_3209_ == 0 {
                        v___x_3204_ = v___x_3175_;
                        v_isShared_3205_ = v_isSharedCheck_3209_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3202_);
                        lean_dec(v___x_3175_);
                        v___x_3204_ = lean_box(0);
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
                    v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3186_);
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
                    v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
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
                    v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
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
    mut v_e_3210_: *mut LeanObject,
    mut v_a_3211_: *mut LeanObject,
    mut v_a_3212_: *mut LeanObject,
    mut v_a_3213_: *mut LeanObject,
    mut v_a_3214_: *mut LeanObject,
    mut v_a_3215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3216_: *mut LeanObject = core::ptr::null_mut();
    v_res_3216_ = l_Lean_Meta_instReduceEvalMVarId___private__1(
        v_e_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_,
    );
    lean_dec(v_a_3214_);
    lean_dec_ref(v_a_3213_);
    lean_dec(v_a_3212_);
    lean_dec_ref(v_a_3211_);
    return v_res_3216_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalMVarId___lam__0(
    mut v_e_3217_: *mut LeanObject,
    mut v___y_3218_: *mut LeanObject,
    mut v___y_3219_: *mut LeanObject,
    mut v___y_3220_: *mut LeanObject,
    mut v___y_3221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: u8 = 0;
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3237_: u8 = 0;
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3241_: u8 = 0;
    let mut v_a_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3245_: u8 = 0;
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3249_: u8 = 0;
    let mut v_a_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3253_: u8 = 0;
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3257_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_3221_);
                lean_inc_ref(v___y_3220_);
                lean_inc(v___y_3219_);
                lean_inc_ref(v___y_3218_);
                v___x_3223_ = lean_whnf(
                    v_e_3217_,
                    v___y_3218_,
                    v___y_3219_,
                    v___y_3220_,
                    v___y_3221_,
                );
                if lean_obj_tag(v___x_3223_) == 0 {
                    v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
                    lean_inc(v_a_3224_);
                    lean_dec_ref_known(v___x_3223_, 1);
                    v___x_3225_ = l_Lean_Meta_instReduceEvalMVarId___private__1___closed__1;
                    v___x_3226_ = lean_unsigned_to_nat(1);
                    v___x_3227_ = l_Lean_Expr_isAppOfArity(v_a_3224_, v___x_3225_, v___x_3226_);
                    if v___x_3227_ == 0 {
                        v___x_3228_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_3224_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
                        return v___x_3228_;
                    } else {
                        v___x_3229_ = l_Lean_Meta_instReduceEvalName___closed__0;
                        v___x_3230_ = l_Lean_Expr_getAppNumArgs(v_a_3224_);
                        v___x_3231_ = lean_nat_sub(v___x_3230_, v___x_3226_);
                        lean_dec(v___x_3230_);
                        v___x_3232_ = l_Lean_Expr_getRevArg_x21(v_a_3224_, v___x_3231_);
                        lean_dec(v_a_3224_);
                        v___x_3233_ = l_Lean_Meta_reduceEval___redArg(
                            v___x_3229_,
                            v___x_3232_,
                            v___y_3218_,
                            v___y_3219_,
                            v___y_3220_,
                            v___y_3221_,
                        );
                        if lean_obj_tag(v___x_3233_) == 0 {
                            v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
                            v_isSharedCheck_3241_ = (!lean_is_exclusive(v___x_3233_)) as u8;
                            if v_isSharedCheck_3241_ == 0 {
                                v___x_3236_ = v___x_3233_;
                                v_isShared_3237_ = v_isSharedCheck_3241_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3234_);
                                lean_dec(v___x_3233_);
                                v___x_3236_ = lean_box(0);
                                v_isShared_3237_ = v_isSharedCheck_3241_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_3242_ = lean_ctor_get(v___x_3233_, 0);
                            v_isSharedCheck_3249_ = (!lean_is_exclusive(v___x_3233_)) as u8;
                            if v_isSharedCheck_3249_ == 0 {
                                v___x_3244_ = v___x_3233_;
                                v_isShared_3245_ = v_isSharedCheck_3249_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_3242_);
                                lean_dec(v___x_3233_);
                                v___x_3244_ = lean_box(0);
                                v_isShared_3245_ = v_isSharedCheck_3249_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_3250_ = lean_ctor_get(v___x_3223_, 0);
                    v_isSharedCheck_3257_ = (!lean_is_exclusive(v___x_3223_)) as u8;
                    if v_isSharedCheck_3257_ == 0 {
                        v___x_3252_ = v___x_3223_;
                        v_isShared_3253_ = v_isSharedCheck_3257_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3250_);
                        lean_dec(v___x_3223_);
                        v___x_3252_ = lean_box(0);
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
                    v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
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
                    v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
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
                    v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_a_3250_);
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
    mut v_e_3258_: *mut LeanObject,
    mut v___y_3259_: *mut LeanObject,
    mut v___y_3260_: *mut LeanObject,
    mut v___y_3261_: *mut LeanObject,
    mut v___y_3262_: *mut LeanObject,
    mut v___y_3263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3264_: *mut LeanObject = core::ptr::null_mut();
    v_res_3264_ = l_Lean_Meta_instReduceEvalMVarId___lam__0(
        v_e_3258_,
        v___y_3259_,
        v___y_3260_,
        v___y_3261_,
        v___y_3262_,
    );
    lean_dec(v___y_3262_);
    lean_dec_ref(v___y_3261_);
    lean_dec(v___y_3260_);
    lean_dec_ref(v___y_3259_);
    return v_res_3264_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalLevelMVarId___private__1(
    mut v_e_3272_: *mut LeanObject,
    mut v_a_3273_: *mut LeanObject,
    mut v_a_3274_: *mut LeanObject,
    mut v_a_3275_: *mut LeanObject,
    mut v_a_3276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: u8 = 0;
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3292_: u8 = 0;
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3296_: u8 = 0;
    let mut v_a_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3300_: u8 = 0;
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3304_: u8 = 0;
    let mut v_a_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3308_: u8 = 0;
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3312_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_3276_);
                lean_inc_ref(v_a_3275_);
                lean_inc(v_a_3274_);
                lean_inc_ref(v_a_3273_);
                v___x_3278_ = lean_whnf(v_e_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
                if lean_obj_tag(v___x_3278_) == 0 {
                    v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
                    lean_inc(v_a_3279_);
                    lean_dec_ref_known(v___x_3278_, 1);
                    v___x_3280_ = l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1;
                    v___x_3281_ = lean_unsigned_to_nat(1);
                    v___x_3282_ = l_Lean_Expr_isAppOfArity(v_a_3279_, v___x_3280_, v___x_3281_);
                    if v___x_3282_ == 0 {
                        v___x_3283_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_3279_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
                        return v___x_3283_;
                    } else {
                        v___x_3284_ = l_Lean_Meta_instReduceEvalName___closed__0;
                        v___x_3285_ = l_Lean_Expr_getAppNumArgs(v_a_3279_);
                        v___x_3286_ = lean_nat_sub(v___x_3285_, v___x_3281_);
                        lean_dec(v___x_3285_);
                        v___x_3287_ = l_Lean_Expr_getRevArg_x21(v_a_3279_, v___x_3286_);
                        lean_dec(v_a_3279_);
                        v___x_3288_ = l_Lean_Meta_reduceEval___redArg(
                            v___x_3284_,
                            v___x_3287_,
                            v_a_3273_,
                            v_a_3274_,
                            v_a_3275_,
                            v_a_3276_,
                        );
                        if lean_obj_tag(v___x_3288_) == 0 {
                            v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
                            v_isSharedCheck_3296_ = (!lean_is_exclusive(v___x_3288_)) as u8;
                            if v_isSharedCheck_3296_ == 0 {
                                v___x_3291_ = v___x_3288_;
                                v_isShared_3292_ = v_isSharedCheck_3296_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3289_);
                                lean_dec(v___x_3288_);
                                v___x_3291_ = lean_box(0);
                                v_isShared_3292_ = v_isSharedCheck_3296_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_3297_ = lean_ctor_get(v___x_3288_, 0);
                            v_isSharedCheck_3304_ = (!lean_is_exclusive(v___x_3288_)) as u8;
                            if v_isSharedCheck_3304_ == 0 {
                                v___x_3299_ = v___x_3288_;
                                v_isShared_3300_ = v_isSharedCheck_3304_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_3297_);
                                lean_dec(v___x_3288_);
                                v___x_3299_ = lean_box(0);
                                v_isShared_3300_ = v_isSharedCheck_3304_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_3305_ = lean_ctor_get(v___x_3278_, 0);
                    v_isSharedCheck_3312_ = (!lean_is_exclusive(v___x_3278_)) as u8;
                    if v_isSharedCheck_3312_ == 0 {
                        v___x_3307_ = v___x_3278_;
                        v_isShared_3308_ = v_isSharedCheck_3312_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3305_);
                        lean_dec(v___x_3278_);
                        v___x_3307_ = lean_box(0);
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
                    v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
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
                    v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
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
                    v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
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
    mut v_e_3313_: *mut LeanObject,
    mut v_a_3314_: *mut LeanObject,
    mut v_a_3315_: *mut LeanObject,
    mut v_a_3316_: *mut LeanObject,
    mut v_a_3317_: *mut LeanObject,
    mut v_a_3318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3319_: *mut LeanObject = core::ptr::null_mut();
    v_res_3319_ = l_Lean_Meta_instReduceEvalLevelMVarId___private__1(
        v_e_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_,
    );
    lean_dec(v_a_3317_);
    lean_dec_ref(v_a_3316_);
    lean_dec(v_a_3315_);
    lean_dec_ref(v_a_3314_);
    return v_res_3319_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalLevelMVarId___lam__0(
    mut v_e_3320_: *mut LeanObject,
    mut v___y_3321_: *mut LeanObject,
    mut v___y_3322_: *mut LeanObject,
    mut v___y_3323_: *mut LeanObject,
    mut v___y_3324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: u8 = 0;
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3340_: u8 = 0;
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3344_: u8 = 0;
    let mut v_a_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3348_: u8 = 0;
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3352_: u8 = 0;
    let mut v_a_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3356_: u8 = 0;
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3360_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_3324_);
                lean_inc_ref(v___y_3323_);
                lean_inc(v___y_3322_);
                lean_inc_ref(v___y_3321_);
                v___x_3326_ = lean_whnf(
                    v_e_3320_,
                    v___y_3321_,
                    v___y_3322_,
                    v___y_3323_,
                    v___y_3324_,
                );
                if lean_obj_tag(v___x_3326_) == 0 {
                    v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
                    lean_inc(v_a_3327_);
                    lean_dec_ref_known(v___x_3326_, 1);
                    v___x_3328_ = l_Lean_Meta_instReduceEvalLevelMVarId___private__1___closed__1;
                    v___x_3329_ = lean_unsigned_to_nat(1);
                    v___x_3330_ = l_Lean_Expr_isAppOfArity(v_a_3327_, v___x_3328_, v___x_3329_);
                    if v___x_3330_ == 0 {
                        v___x_3331_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_3327_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
                        return v___x_3331_;
                    } else {
                        v___x_3332_ = l_Lean_Meta_instReduceEvalName___closed__0;
                        v___x_3333_ = l_Lean_Expr_getAppNumArgs(v_a_3327_);
                        v___x_3334_ = lean_nat_sub(v___x_3333_, v___x_3329_);
                        lean_dec(v___x_3333_);
                        v___x_3335_ = l_Lean_Expr_getRevArg_x21(v_a_3327_, v___x_3334_);
                        lean_dec(v_a_3327_);
                        v___x_3336_ = l_Lean_Meta_reduceEval___redArg(
                            v___x_3332_,
                            v___x_3335_,
                            v___y_3321_,
                            v___y_3322_,
                            v___y_3323_,
                            v___y_3324_,
                        );
                        if lean_obj_tag(v___x_3336_) == 0 {
                            v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
                            v_isSharedCheck_3344_ = (!lean_is_exclusive(v___x_3336_)) as u8;
                            if v_isSharedCheck_3344_ == 0 {
                                v___x_3339_ = v___x_3336_;
                                v_isShared_3340_ = v_isSharedCheck_3344_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3337_);
                                lean_dec(v___x_3336_);
                                v___x_3339_ = lean_box(0);
                                v_isShared_3340_ = v_isSharedCheck_3344_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_3345_ = lean_ctor_get(v___x_3336_, 0);
                            v_isSharedCheck_3352_ = (!lean_is_exclusive(v___x_3336_)) as u8;
                            if v_isSharedCheck_3352_ == 0 {
                                v___x_3347_ = v___x_3336_;
                                v_isShared_3348_ = v_isSharedCheck_3352_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_3345_);
                                lean_dec(v___x_3336_);
                                v___x_3347_ = lean_box(0);
                                v_isShared_3348_ = v_isSharedCheck_3352_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_3353_ = lean_ctor_get(v___x_3326_, 0);
                    v_isSharedCheck_3360_ = (!lean_is_exclusive(v___x_3326_)) as u8;
                    if v_isSharedCheck_3360_ == 0 {
                        v___x_3355_ = v___x_3326_;
                        v_isShared_3356_ = v_isSharedCheck_3360_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3353_);
                        lean_dec(v___x_3326_);
                        v___x_3355_ = lean_box(0);
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
                    v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3337_);
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
                    v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
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
                    v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
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
    mut v_e_3361_: *mut LeanObject,
    mut v___y_3362_: *mut LeanObject,
    mut v___y_3363_: *mut LeanObject,
    mut v___y_3364_: *mut LeanObject,
    mut v___y_3365_: *mut LeanObject,
    mut v___y_3366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3367_: *mut LeanObject = core::ptr::null_mut();
    v_res_3367_ = l_Lean_Meta_instReduceEvalLevelMVarId___lam__0(
        v_e_3361_,
        v___y_3362_,
        v___y_3363_,
        v___y_3364_,
        v___y_3365_,
    );
    lean_dec(v___y_3365_);
    lean_dec_ref(v___y_3364_);
    lean_dec(v___y_3363_);
    lean_dec_ref(v___y_3362_);
    return v_res_3367_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalFVarId___private__1(
    mut v_e_3375_: *mut LeanObject,
    mut v_a_3376_: *mut LeanObject,
    mut v_a_3377_: *mut LeanObject,
    mut v_a_3378_: *mut LeanObject,
    mut v_a_3379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: u8 = 0;
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3395_: u8 = 0;
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3399_: u8 = 0;
    let mut v_a_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3403_: u8 = 0;
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3407_: u8 = 0;
    let mut v_a_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3411_: u8 = 0;
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_3379_);
                lean_inc_ref(v_a_3378_);
                lean_inc(v_a_3377_);
                lean_inc_ref(v_a_3376_);
                v___x_3381_ = lean_whnf(v_e_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_);
                if lean_obj_tag(v___x_3381_) == 0 {
                    v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
                    lean_inc(v_a_3382_);
                    lean_dec_ref_known(v___x_3381_, 1);
                    v___x_3383_ = l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1;
                    v___x_3384_ = lean_unsigned_to_nat(1);
                    v___x_3385_ = l_Lean_Expr_isAppOfArity(v_a_3382_, v___x_3383_, v___x_3384_);
                    if v___x_3385_ == 0 {
                        v___x_3386_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_3382_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_);
                        return v___x_3386_;
                    } else {
                        v___x_3387_ = l_Lean_Meta_instReduceEvalName___closed__0;
                        v___x_3388_ = l_Lean_Expr_getAppNumArgs(v_a_3382_);
                        v___x_3389_ = lean_nat_sub(v___x_3388_, v___x_3384_);
                        lean_dec(v___x_3388_);
                        v___x_3390_ = l_Lean_Expr_getRevArg_x21(v_a_3382_, v___x_3389_);
                        lean_dec(v_a_3382_);
                        v___x_3391_ = l_Lean_Meta_reduceEval___redArg(
                            v___x_3387_,
                            v___x_3390_,
                            v_a_3376_,
                            v_a_3377_,
                            v_a_3378_,
                            v_a_3379_,
                        );
                        if lean_obj_tag(v___x_3391_) == 0 {
                            v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
                            v_isSharedCheck_3399_ = (!lean_is_exclusive(v___x_3391_)) as u8;
                            if v_isSharedCheck_3399_ == 0 {
                                v___x_3394_ = v___x_3391_;
                                v_isShared_3395_ = v_isSharedCheck_3399_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3392_);
                                lean_dec(v___x_3391_);
                                v___x_3394_ = lean_box(0);
                                v_isShared_3395_ = v_isSharedCheck_3399_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_3400_ = lean_ctor_get(v___x_3391_, 0);
                            v_isSharedCheck_3407_ = (!lean_is_exclusive(v___x_3391_)) as u8;
                            if v_isSharedCheck_3407_ == 0 {
                                v___x_3402_ = v___x_3391_;
                                v_isShared_3403_ = v_isSharedCheck_3407_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_3400_);
                                lean_dec(v___x_3391_);
                                v___x_3402_ = lean_box(0);
                                v_isShared_3403_ = v_isSharedCheck_3407_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_3408_ = lean_ctor_get(v___x_3381_, 0);
                    v_isSharedCheck_3415_ = (!lean_is_exclusive(v___x_3381_)) as u8;
                    if v_isSharedCheck_3415_ == 0 {
                        v___x_3410_ = v___x_3381_;
                        v_isShared_3411_ = v_isSharedCheck_3415_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3408_);
                        lean_dec(v___x_3381_);
                        v___x_3410_ = lean_box(0);
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
                    v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3392_);
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
                    v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
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
                    v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
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
    mut v_e_3416_: *mut LeanObject,
    mut v_a_3417_: *mut LeanObject,
    mut v_a_3418_: *mut LeanObject,
    mut v_a_3419_: *mut LeanObject,
    mut v_a_3420_: *mut LeanObject,
    mut v_a_3421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3422_: *mut LeanObject = core::ptr::null_mut();
    v_res_3422_ = l_Lean_Meta_instReduceEvalFVarId___private__1(
        v_e_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_,
    );
    lean_dec(v_a_3420_);
    lean_dec_ref(v_a_3419_);
    lean_dec(v_a_3418_);
    lean_dec_ref(v_a_3417_);
    return v_res_3422_;
}
pub unsafe fn l_Lean_Meta_instReduceEvalFVarId___lam__0(
    mut v_e_3423_: *mut LeanObject,
    mut v___y_3424_: *mut LeanObject,
    mut v___y_3425_: *mut LeanObject,
    mut v___y_3426_: *mut LeanObject,
    mut v___y_3427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: u8 = 0;
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3443_: u8 = 0;
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3447_: u8 = 0;
    let mut v_a_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3451_: u8 = 0;
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut v_a_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3459_: u8 = 0;
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_3427_);
                lean_inc_ref(v___y_3426_);
                lean_inc(v___y_3425_);
                lean_inc_ref(v___y_3424_);
                v___x_3429_ = lean_whnf(
                    v_e_3423_,
                    v___y_3424_,
                    v___y_3425_,
                    v___y_3426_,
                    v___y_3427_,
                );
                if lean_obj_tag(v___x_3429_) == 0 {
                    v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
                    lean_inc(v_a_3430_);
                    lean_dec_ref_known(v___x_3429_, 1);
                    v___x_3431_ = l_Lean_Meta_instReduceEvalFVarId___private__1___closed__1;
                    v___x_3432_ = lean_unsigned_to_nat(1);
                    v___x_3433_ = l_Lean_Expr_isAppOfArity(v_a_3430_, v___x_3431_, v___x_3432_);
                    if v___x_3433_ == 0 {
                        v___x_3434_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(v_a_3430_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
                        return v___x_3434_;
                    } else {
                        v___x_3435_ = l_Lean_Meta_instReduceEvalName___closed__0;
                        v___x_3436_ = l_Lean_Expr_getAppNumArgs(v_a_3430_);
                        v___x_3437_ = lean_nat_sub(v___x_3436_, v___x_3432_);
                        lean_dec(v___x_3436_);
                        v___x_3438_ = l_Lean_Expr_getRevArg_x21(v_a_3430_, v___x_3437_);
                        lean_dec(v_a_3430_);
                        v___x_3439_ = l_Lean_Meta_reduceEval___redArg(
                            v___x_3435_,
                            v___x_3438_,
                            v___y_3424_,
                            v___y_3425_,
                            v___y_3426_,
                            v___y_3427_,
                        );
                        if lean_obj_tag(v___x_3439_) == 0 {
                            v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
                            v_isSharedCheck_3447_ = (!lean_is_exclusive(v___x_3439_)) as u8;
                            if v_isSharedCheck_3447_ == 0 {
                                v___x_3442_ = v___x_3439_;
                                v_isShared_3443_ = v_isSharedCheck_3447_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3440_);
                                lean_dec(v___x_3439_);
                                v___x_3442_ = lean_box(0);
                                v_isShared_3443_ = v_isSharedCheck_3447_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_3448_ = lean_ctor_get(v___x_3439_, 0);
                            v_isSharedCheck_3455_ = (!lean_is_exclusive(v___x_3439_)) as u8;
                            if v_isSharedCheck_3455_ == 0 {
                                v___x_3450_ = v___x_3439_;
                                v_isShared_3451_ = v_isSharedCheck_3455_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_3448_);
                                lean_dec(v___x_3439_);
                                v___x_3450_ = lean_box(0);
                                v_isShared_3451_ = v_isSharedCheck_3455_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_3456_ = lean_ctor_get(v___x_3429_, 0);
                    v_isSharedCheck_3463_ = (!lean_is_exclusive(v___x_3429_)) as u8;
                    if v_isSharedCheck_3463_ == 0 {
                        v___x_3458_ = v___x_3429_;
                        v_isShared_3459_ = v_isSharedCheck_3463_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3456_);
                        lean_dec(v___x_3429_);
                        v___x_3458_ = lean_box(0);
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
                    v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3440_);
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
                    v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
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
                    v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
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
    mut v_e_3464_: *mut LeanObject,
    mut v___y_3465_: *mut LeanObject,
    mut v___y_3466_: *mut LeanObject,
    mut v___y_3467_: *mut LeanObject,
    mut v___y_3468_: *mut LeanObject,
    mut v___y_3469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3470_: *mut LeanObject = core::ptr::null_mut();
    v_res_3470_ = l_Lean_Meta_instReduceEvalFVarId___lam__0(
        v_e_3464_,
        v___y_3465_,
        v___y_3466_,
        v___y_3467_,
        v___y_3468_,
    );
    lean_dec(v___y_3468_);
    lean_dec_ref(v___y_3467_);
    lean_dec(v___y_3466_);
    lean_dec_ref(v___y_3465_);
    return v_res_3470_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_ReduceEval(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Offset(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_ReduceEval(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_ReduceEval(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Offset(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ReduceEval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_ReduceEval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_ReduceEval(builtin);
}
