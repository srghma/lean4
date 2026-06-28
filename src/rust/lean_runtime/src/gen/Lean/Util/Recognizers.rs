// Lean compiler output
// Module: Lean.Util.Recognizers
// Imports: Lean.Environment
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
    l_Lean_Name_mkStr5, l_Lean_Name_mkStr6, l_Lean_Name_mkStr7, l_Lean_Name_mkStr8,
    l_Lean_Name_num___override, l_Lean_Name_str___override,
};
use crate::r#gen::Lean::Environment::{
    initialize_Lean_Environment, runtime_initialize_Lean_Environment,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appArg_x21_x27, l_Lean_Expr_appFn_x21,
    l_Lean_Expr_appFn_x21_x27, l_Lean_Expr_hasLooseBVars, l_Lean_Expr_isAppOfArity,
    l_Lean_Expr_isAppOfArity_x27, l_Lean_Expr_nat_x3f, l_Lean_Expr_rawNatLit_x3f,
};
use crate::lean_imports_rs::Init::Prelude::lean_string_dec_eq;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lean_Expr_eq_x3f___closed__0_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [69, 113, 0],
};
static mut l_Lean_Expr_eq_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_eq_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Expr_eq_x3f___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Expr_eq_x3f___closed__0_value) as *mut LeanObject,
        16122875713692181903 as *mut LeanObject,
    ],
};
static mut l_Lean_Expr_eq_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_eq_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Expr_ne_x3f___closed__0_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [78, 101, 0],
};
static mut l_Lean_Expr_ne_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_ne_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Expr_ne_x3f___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Expr_ne_x3f___closed__0_value) as *mut LeanObject,
        6695605208187598753 as *mut LeanObject,
    ],
};
static mut l_Lean_Expr_ne_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_ne_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Expr_iff_x3f___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [73, 102, 102, 0],
};
static mut l_Lean_Expr_iff_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_iff_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Expr_iff_x3f___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Expr_iff_x3f___closed__0_value) as *mut LeanObject,
        9917798623386220051 as *mut LeanObject,
    ],
};
static mut l_Lean_Expr_iff_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_iff_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Expr_not_x3f___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [78, 111, 116, 0],
};
static mut l_Lean_Expr_not_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_not_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Expr_not_x3f___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Expr_not_x3f___closed__0_value) as *mut LeanObject,
        16612019923665488825 as *mut LeanObject,
    ],
};
static mut l_Lean_Expr_not_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_not_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Expr_and_x3f___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [65, 110, 100, 0],
};
static mut l_Lean_Expr_and_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_and_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Expr_and_x3f___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Expr_and_x3f___closed__0_value) as *mut LeanObject,
        9743492140944907313 as *mut LeanObject,
    ],
};
static mut l_Lean_Expr_and_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_and_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Expr_heq_x3f___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [72, 69, 113, 0],
};
static mut l_Lean_Expr_heq_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_heq_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Expr_heq_x3f___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Expr_heq_x3f___closed__0_value) as *mut LeanObject,
        13589827700912665667 as *mut LeanObject,
    ],
};
static mut l_Lean_Expr_heq_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_heq_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Expr_natAdd_x3f___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [78, 97, 116, 0],
};
static mut l_Lean_Expr_natAdd_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_natAdd_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Expr_natAdd_x3f___closed__1_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [97, 100, 100, 0],
};
static mut l_Lean_Expr_natAdd_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_natAdd_x3f___closed__1_value) as *mut LeanObject;
static l_Lean_Expr_natAdd_x3f___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Expr_natAdd_x3f___closed__0_value) as *mut LeanObject,
        11442535297760353691 as *mut LeanObject,
    ],
};
pub static l_Lean_Expr_natAdd_x3f___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Expr_natAdd_x3f___closed__2_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Expr_natAdd_x3f___closed__1_value) as *mut LeanObject,
        17073733886952259026 as *mut LeanObject,
    ],
};
static mut l_Lean_Expr_natAdd_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_natAdd_x3f___closed__2_value) as *mut LeanObject;
pub static l_Lean_Expr_isIte___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [105, 116, 101, 0],
};
static mut l_Lean_Expr_isIte___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isIte___closed__0_value) as *mut LeanObject;
pub static l_Lean_Expr_isIte___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Expr_isIte___closed__0_value) as *mut LeanObject,
        18356704233129443855 as *mut LeanObject,
    ],
};
static mut l_Lean_Expr_isIte___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isIte___closed__1_value) as *mut LeanObject;
pub static l_Lean_Expr_isDIte___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [100, 105, 116, 101, 0],
};
static mut l_Lean_Expr_isDIte___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isDIte___closed__0_value) as *mut LeanObject;
pub static l_Lean_Expr_isDIte___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Expr_isDIte___closed__0_value) as *mut LeanObject,
        8391571994004792969 as *mut LeanObject,
    ],
};
static mut l_Lean_Expr_isDIte___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isDIte___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__0_value:
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
static mut l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__1_value:
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
static mut l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__1_value
) as *mut LeanObject;
static l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__2_value_aux_0:
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
            l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__0_value
        ) as *mut LeanObject,
        9582258842178272501 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__2_value:
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
            l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__2_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__1_value
        ) as *mut LeanObject,
        18135193680607614554 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__3_value:
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
static mut l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__3_value
) as *mut LeanObject;
static l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__4_value_aux_0:
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
            l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__0_value
        ) as *mut LeanObject,
        9582258842178272501 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__4_value:
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
            l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__3_value
        ) as *mut LeanObject,
        8614124190858717794 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__4_value
) as *mut LeanObject;
pub static l_Lean_Expr_arrayLit_x3f___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [116, 111, 65, 114, 114, 97, 121, 0],
};
static mut l_Lean_Expr_arrayLit_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_arrayLit_x3f___closed__0_value) as *mut LeanObject;
static l_Lean_Expr_arrayLit_x3f___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
            l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__0_value
        ) as *mut LeanObject,
        9582258842178272501 as *mut LeanObject,
    ],
};
pub static l_Lean_Expr_arrayLit_x3f___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Expr_arrayLit_x3f___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Expr_arrayLit_x3f___closed__0_value) as *mut LeanObject,
        8414467900391110369 as *mut LeanObject,
    ],
};
static mut l_Lean_Expr_arrayLit_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_arrayLit_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Expr_prod_x3f___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [80, 114, 111, 100, 0],
};
static mut l_Lean_Expr_prod_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_prod_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Expr_prod_x3f___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Expr_prod_x3f___closed__0_value) as *mut LeanObject,
        15289851429949568889 as *mut LeanObject,
    ],
};
static mut l_Lean_Expr_prod_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_prod_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Expr_name_x3f___closed__0_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_Expr_name_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Expr_name_x3f___closed__1_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_Expr_name_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Expr_name_x3f___closed__2_value: LeanStringObject<10> = LeanStringObject {
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
static mut l_Lean_Expr_name_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__2_value) as *mut LeanObject;
pub static l_Lean_Expr_name_x3f___closed__3_value: LeanStringObject<4> = LeanStringObject {
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
static mut l_Lean_Expr_name_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__3_value) as *mut LeanObject;
pub static l_Lean_Expr_name_x3f___closed__4_value: LeanStringObject<4> = LeanStringObject {
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
static mut l_Lean_Expr_name_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__4_value) as *mut LeanObject;
pub static l_Lean_Expr_name_x3f___closed__5_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [109, 107, 83, 116, 114, 50, 0],
};
static mut l_Lean_Expr_name_x3f___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__5_value) as *mut LeanObject;
pub static l_Lean_Expr_name_x3f___closed__6_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [109, 107, 83, 116, 114, 51, 0],
};
static mut l_Lean_Expr_name_x3f___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__6_value) as *mut LeanObject;
pub static l_Lean_Expr_name_x3f___closed__7_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [109, 107, 83, 116, 114, 52, 0],
};
static mut l_Lean_Expr_name_x3f___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__7_value) as *mut LeanObject;
pub static l_Lean_Expr_name_x3f___closed__8_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [109, 107, 83, 116, 114, 53, 0],
};
static mut l_Lean_Expr_name_x3f___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__8_value) as *mut LeanObject;
pub static l_Lean_Expr_name_x3f___closed__9_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [109, 107, 83, 116, 114, 54, 0],
};
static mut l_Lean_Expr_name_x3f___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__9_value) as *mut LeanObject;
pub static l_Lean_Expr_name_x3f___closed__10_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [109, 107, 83, 116, 114, 55, 0],
};
static mut l_Lean_Expr_name_x3f___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__10_value) as *mut LeanObject;
pub static l_Lean_Expr_name_x3f___closed__11_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [109, 107, 83, 116, 114, 56, 0],
};
static mut l_Lean_Expr_name_x3f___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__11_value) as *mut LeanObject;
pub static l_Lean_Expr_name_x3f___closed__12_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [109, 107, 83, 116, 114, 49, 0],
};
static mut l_Lean_Expr_name_x3f___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__12_value) as *mut LeanObject;
pub unsafe fn l_Lean_Expr_const_x3f(mut v_e_795_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_e_795_) == 4 {
        let mut v_declName_796_: *mut LeanObject = core::ptr::null_mut();
        let mut v_us_797_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
        v_declName_796_ = lean_ctor_get(v_e_795_, 0);
        v_us_797_ = lean_ctor_get(v_e_795_, 1);
        lean_inc(v_us_797_);
        lean_inc(v_declName_796_);
        v___x_798_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_798_, 0, v_declName_796_);
        lean_ctor_set(v___x_798_, 1, v_us_797_);
        v___x_799_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_799_, 0, v___x_798_);
        return v___x_799_;
    } else {
        let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
        v___x_800_ = lean_box(0);
        return v___x_800_;
    }
}
pub unsafe fn l_Lean_Expr_const_x3f___boxed(mut v_e_801_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_802_: *mut LeanObject = core::ptr::null_mut();
    v_res_802_ = l_Lean_Expr_const_x3f(v_e_801_);
    lean_dec_ref(v_e_801_);
    return v_res_802_;
}
pub unsafe fn l_Lean_Expr_app1_x3f(
    mut v_e_803_: *mut LeanObject,
    mut v_fName_804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: u8 = 0;
    v___x_805_ = lean_unsigned_to_nat(1);
    v___x_806_ = l_Lean_Expr_isAppOfArity(v_e_803_, v_fName_804_, v___x_805_);
    if v___x_806_ == 0 {
        let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
        v___x_807_ = lean_box(0);
        return v___x_807_;
    } else {
        let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
        v___x_808_ = l_Lean_Expr_appArg_x21(v_e_803_);
        v___x_809_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_809_, 0, v___x_808_);
        return v___x_809_;
    }
}
pub unsafe fn l_Lean_Expr_app1_x3f___boxed(
    mut v_e_810_: *mut LeanObject,
    mut v_fName_811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_812_: *mut LeanObject = core::ptr::null_mut();
    v_res_812_ = l_Lean_Expr_app1_x3f(v_e_810_, v_fName_811_);
    lean_dec(v_fName_811_);
    lean_dec_ref(v_e_810_);
    return v_res_812_;
}
pub unsafe fn l_Lean_Expr_app2_x3f(
    mut v_e_813_: *mut LeanObject,
    mut v_fName_814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: u8 = 0;
    v___x_815_ = lean_unsigned_to_nat(2);
    v___x_816_ = l_Lean_Expr_isAppOfArity(v_e_813_, v_fName_814_, v___x_815_);
    if v___x_816_ == 0 {
        let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
        v___x_817_ = lean_box(0);
        return v___x_817_;
    } else {
        let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
        v___x_818_ = l_Lean_Expr_appFn_x21(v_e_813_);
        v___x_819_ = l_Lean_Expr_appArg_x21(v___x_818_);
        lean_dec_ref(v___x_818_);
        v___x_820_ = l_Lean_Expr_appArg_x21(v_e_813_);
        v___x_821_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_821_, 0, v___x_819_);
        lean_ctor_set(v___x_821_, 1, v___x_820_);
        v___x_822_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_822_, 0, v___x_821_);
        return v___x_822_;
    }
}
pub unsafe fn l_Lean_Expr_app2_x3f___boxed(
    mut v_e_823_: *mut LeanObject,
    mut v_fName_824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_825_: *mut LeanObject = core::ptr::null_mut();
    v_res_825_ = l_Lean_Expr_app2_x3f(v_e_823_, v_fName_824_);
    lean_dec(v_fName_824_);
    lean_dec_ref(v_e_823_);
    return v_res_825_;
}
pub unsafe fn l_Lean_Expr_app3_x3f(
    mut v_e_826_: *mut LeanObject,
    mut v_fName_827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_829_: u8 = 0;
    v___x_828_ = lean_unsigned_to_nat(3);
    v___x_829_ = l_Lean_Expr_isAppOfArity(v_e_826_, v_fName_827_, v___x_828_);
    if v___x_829_ == 0 {
        let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
        v___x_830_ = lean_box(0);
        return v___x_830_;
    } else {
        let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
        v___x_831_ = l_Lean_Expr_appFn_x21(v_e_826_);
        v___x_832_ = l_Lean_Expr_appFn_x21(v___x_831_);
        v___x_833_ = l_Lean_Expr_appArg_x21(v___x_832_);
        lean_dec_ref(v___x_832_);
        v___x_834_ = l_Lean_Expr_appArg_x21(v___x_831_);
        lean_dec_ref(v___x_831_);
        v___x_835_ = l_Lean_Expr_appArg_x21(v_e_826_);
        v___x_836_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_836_, 0, v___x_834_);
        lean_ctor_set(v___x_836_, 1, v___x_835_);
        v___x_837_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_837_, 0, v___x_833_);
        lean_ctor_set(v___x_837_, 1, v___x_836_);
        v___x_838_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_838_, 0, v___x_837_);
        return v___x_838_;
    }
}
pub unsafe fn l_Lean_Expr_app3_x3f___boxed(
    mut v_e_839_: *mut LeanObject,
    mut v_fName_840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_841_: *mut LeanObject = core::ptr::null_mut();
    v_res_841_ = l_Lean_Expr_app3_x3f(v_e_839_, v_fName_840_);
    lean_dec(v_fName_840_);
    lean_dec_ref(v_e_839_);
    return v_res_841_;
}
pub unsafe fn l_Lean_Expr_app4_x3f(
    mut v_e_842_: *mut LeanObject,
    mut v_fName_843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: u8 = 0;
    v___x_844_ = lean_unsigned_to_nat(4);
    v___x_845_ = l_Lean_Expr_isAppOfArity(v_e_842_, v_fName_843_, v___x_844_);
    if v___x_845_ == 0 {
        let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
        v___x_846_ = lean_box(0);
        return v___x_846_;
    } else {
        let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
        v___x_847_ = l_Lean_Expr_appFn_x21(v_e_842_);
        v___x_848_ = l_Lean_Expr_appFn_x21(v___x_847_);
        v___x_849_ = l_Lean_Expr_appFn_x21(v___x_848_);
        v___x_850_ = l_Lean_Expr_appArg_x21(v___x_849_);
        lean_dec_ref(v___x_849_);
        v___x_851_ = l_Lean_Expr_appArg_x21(v___x_848_);
        lean_dec_ref(v___x_848_);
        v___x_852_ = l_Lean_Expr_appArg_x21(v___x_847_);
        lean_dec_ref(v___x_847_);
        v___x_853_ = l_Lean_Expr_appArg_x21(v_e_842_);
        v___x_854_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_854_, 0, v___x_852_);
        lean_ctor_set(v___x_854_, 1, v___x_853_);
        v___x_855_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_855_, 0, v___x_851_);
        lean_ctor_set(v___x_855_, 1, v___x_854_);
        v___x_856_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_856_, 0, v___x_850_);
        lean_ctor_set(v___x_856_, 1, v___x_855_);
        v___x_857_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_857_, 0, v___x_856_);
        return v___x_857_;
    }
}
pub unsafe fn l_Lean_Expr_app4_x3f___boxed(
    mut v_e_858_: *mut LeanObject,
    mut v_fName_859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_860_: *mut LeanObject = core::ptr::null_mut();
    v_res_860_ = l_Lean_Expr_app4_x3f(v_e_858_, v_fName_859_);
    lean_dec(v_fName_859_);
    lean_dec_ref(v_e_858_);
    return v_res_860_;
}
pub unsafe fn l_Lean_Expr_eq_x3f(mut v_p_864_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: u8 = 0;
    v___x_865_ = l_Lean_Expr_eq_x3f___closed__1;
    v___x_866_ = lean_unsigned_to_nat(3);
    v___x_867_ = l_Lean_Expr_isAppOfArity(v_p_864_, v___x_865_, v___x_866_);
    if v___x_867_ == 0 {
        let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
        v___x_868_ = lean_box(0);
        return v___x_868_;
    } else {
        let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
        v___x_869_ = l_Lean_Expr_appFn_x21(v_p_864_);
        v___x_870_ = l_Lean_Expr_appFn_x21(v___x_869_);
        v___x_871_ = l_Lean_Expr_appArg_x21(v___x_870_);
        lean_dec_ref(v___x_870_);
        v___x_872_ = l_Lean_Expr_appArg_x21(v___x_869_);
        lean_dec_ref(v___x_869_);
        v___x_873_ = l_Lean_Expr_appArg_x21(v_p_864_);
        v___x_874_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_874_, 0, v___x_872_);
        lean_ctor_set(v___x_874_, 1, v___x_873_);
        v___x_875_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_875_, 0, v___x_871_);
        lean_ctor_set(v___x_875_, 1, v___x_874_);
        v___x_876_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_876_, 0, v___x_875_);
        return v___x_876_;
    }
}
pub unsafe fn l_Lean_Expr_eq_x3f___boxed(mut v_p_877_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_878_: *mut LeanObject = core::ptr::null_mut();
    v_res_878_ = l_Lean_Expr_eq_x3f(v_p_877_);
    lean_dec_ref(v_p_877_);
    return v_res_878_;
}
pub unsafe fn l_Lean_Expr_ne_x3f(mut v_p_882_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: u8 = 0;
    v___x_883_ = l_Lean_Expr_ne_x3f___closed__1;
    v___x_884_ = lean_unsigned_to_nat(3);
    v___x_885_ = l_Lean_Expr_isAppOfArity(v_p_882_, v___x_883_, v___x_884_);
    if v___x_885_ == 0 {
        let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
        v___x_886_ = lean_box(0);
        return v___x_886_;
    } else {
        let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
        v___x_887_ = l_Lean_Expr_appFn_x21(v_p_882_);
        v___x_888_ = l_Lean_Expr_appFn_x21(v___x_887_);
        v___x_889_ = l_Lean_Expr_appArg_x21(v___x_888_);
        lean_dec_ref(v___x_888_);
        v___x_890_ = l_Lean_Expr_appArg_x21(v___x_887_);
        lean_dec_ref(v___x_887_);
        v___x_891_ = l_Lean_Expr_appArg_x21(v_p_882_);
        v___x_892_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_892_, 0, v___x_890_);
        lean_ctor_set(v___x_892_, 1, v___x_891_);
        v___x_893_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_893_, 0, v___x_889_);
        lean_ctor_set(v___x_893_, 1, v___x_892_);
        v___x_894_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_894_, 0, v___x_893_);
        return v___x_894_;
    }
}
pub unsafe fn l_Lean_Expr_ne_x3f___boxed(mut v_p_895_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_896_: *mut LeanObject = core::ptr::null_mut();
    v_res_896_ = l_Lean_Expr_ne_x3f(v_p_895_);
    lean_dec_ref(v_p_895_);
    return v_res_896_;
}
pub unsafe fn l_Lean_Expr_iff_x3f(mut v_p_900_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: u8 = 0;
    v___x_901_ = l_Lean_Expr_iff_x3f___closed__1;
    v___x_902_ = lean_unsigned_to_nat(2);
    v___x_903_ = l_Lean_Expr_isAppOfArity(v_p_900_, v___x_901_, v___x_902_);
    if v___x_903_ == 0 {
        let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
        v___x_904_ = lean_box(0);
        return v___x_904_;
    } else {
        let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
        v___x_905_ = l_Lean_Expr_appFn_x21(v_p_900_);
        v___x_906_ = l_Lean_Expr_appArg_x21(v___x_905_);
        lean_dec_ref(v___x_905_);
        v___x_907_ = l_Lean_Expr_appArg_x21(v_p_900_);
        v___x_908_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_908_, 0, v___x_906_);
        lean_ctor_set(v___x_908_, 1, v___x_907_);
        v___x_909_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_909_, 0, v___x_908_);
        return v___x_909_;
    }
}
pub unsafe fn l_Lean_Expr_iff_x3f___boxed(mut v_p_910_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_911_: *mut LeanObject = core::ptr::null_mut();
    v_res_911_ = l_Lean_Expr_iff_x3f(v_p_910_);
    lean_dec_ref(v_p_910_);
    return v_res_911_;
}
pub unsafe fn l_Lean_Expr_eqOrIff_x3f(mut v_p_912_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: u8 = 0;
    v___x_913_ = l_Lean_Expr_eq_x3f___closed__1;
    v___x_914_ = lean_unsigned_to_nat(3);
    v___x_915_ = l_Lean_Expr_isAppOfArity(v_p_912_, v___x_913_, v___x_914_);
    if v___x_915_ == 0 {
        let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_918_: u8 = 0;
        v___x_916_ = l_Lean_Expr_iff_x3f___closed__1;
        v___x_917_ = lean_unsigned_to_nat(2);
        v___x_918_ = l_Lean_Expr_isAppOfArity(v_p_912_, v___x_916_, v___x_917_);
        if v___x_918_ == 0 {
            let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
            v___x_919_ = lean_box(0);
            return v___x_919_;
        } else {
            let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
            v___x_920_ = l_Lean_Expr_appFn_x21(v_p_912_);
            v___x_921_ = l_Lean_Expr_appArg_x21(v___x_920_);
            lean_dec_ref(v___x_920_);
            v___x_922_ = l_Lean_Expr_appArg_x21(v_p_912_);
            v___x_923_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_923_, 0, v___x_921_);
            lean_ctor_set(v___x_923_, 1, v___x_922_);
            v___x_924_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_924_, 0, v___x_923_);
            return v___x_924_;
        }
    } else {
        let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
        v___x_925_ = l_Lean_Expr_appFn_x21(v_p_912_);
        v___x_926_ = l_Lean_Expr_appArg_x21(v___x_925_);
        lean_dec_ref(v___x_925_);
        v___x_927_ = l_Lean_Expr_appArg_x21(v_p_912_);
        v___x_928_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_928_, 0, v___x_926_);
        lean_ctor_set(v___x_928_, 1, v___x_927_);
        v___x_929_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_929_, 0, v___x_928_);
        return v___x_929_;
    }
}
pub unsafe fn l_Lean_Expr_eqOrIff_x3f___boxed(mut v_p_930_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_931_: *mut LeanObject = core::ptr::null_mut();
    v_res_931_ = l_Lean_Expr_eqOrIff_x3f(v_p_930_);
    lean_dec_ref(v_p_930_);
    return v_res_931_;
}
pub unsafe fn l_Lean_Expr_not_x3f(mut v_p_935_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_938_: u8 = 0;
    v___x_936_ = l_Lean_Expr_not_x3f___closed__1;
    v___x_937_ = lean_unsigned_to_nat(1);
    v___x_938_ = l_Lean_Expr_isAppOfArity(v_p_935_, v___x_936_, v___x_937_);
    if v___x_938_ == 0 {
        let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
        v___x_939_ = lean_box(0);
        return v___x_939_;
    } else {
        let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
        v___x_940_ = l_Lean_Expr_appArg_x21(v_p_935_);
        v___x_941_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_941_, 0, v___x_940_);
        return v___x_941_;
    }
}
pub unsafe fn l_Lean_Expr_not_x3f___boxed(mut v_p_942_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_943_: *mut LeanObject = core::ptr::null_mut();
    v_res_943_ = l_Lean_Expr_not_x3f(v_p_942_);
    lean_dec_ref(v_p_942_);
    return v_res_943_;
}
pub unsafe fn l_Lean_Expr_notNot_x3f(mut v_p_944_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: u8 = 0;
    v___x_945_ = l_Lean_Expr_not_x3f___closed__1;
    v___x_946_ = lean_unsigned_to_nat(1);
    v___x_947_ = l_Lean_Expr_isAppOfArity(v_p_944_, v___x_945_, v___x_946_);
    if v___x_947_ == 0 {
        let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
        v___x_948_ = lean_box(0);
        return v___x_948_;
    } else {
        let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_950_: u8 = 0;
        v___x_949_ = l_Lean_Expr_appArg_x21(v_p_944_);
        v___x_950_ = l_Lean_Expr_isAppOfArity(v___x_949_, v___x_945_, v___x_946_);
        if v___x_950_ == 0 {
            let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___x_949_);
            v___x_951_ = lean_box(0);
            return v___x_951_;
        } else {
            let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
            v___x_952_ = l_Lean_Expr_appArg_x21(v___x_949_);
            lean_dec_ref(v___x_949_);
            v___x_953_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_953_, 0, v___x_952_);
            return v___x_953_;
        }
    }
}
pub unsafe fn l_Lean_Expr_notNot_x3f___boxed(mut v_p_954_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_955_: *mut LeanObject = core::ptr::null_mut();
    v_res_955_ = l_Lean_Expr_notNot_x3f(v_p_954_);
    lean_dec_ref(v_p_954_);
    return v_res_955_;
}
pub unsafe fn l_Lean_Expr_and_x3f(mut v_p_959_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: u8 = 0;
    v___x_960_ = l_Lean_Expr_and_x3f___closed__1;
    v___x_961_ = lean_unsigned_to_nat(2);
    v___x_962_ = l_Lean_Expr_isAppOfArity(v_p_959_, v___x_960_, v___x_961_);
    if v___x_962_ == 0 {
        let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
        v___x_963_ = lean_box(0);
        return v___x_963_;
    } else {
        let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
        v___x_964_ = l_Lean_Expr_appFn_x21(v_p_959_);
        v___x_965_ = l_Lean_Expr_appArg_x21(v___x_964_);
        lean_dec_ref(v___x_964_);
        v___x_966_ = l_Lean_Expr_appArg_x21(v_p_959_);
        v___x_967_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_967_, 0, v___x_965_);
        lean_ctor_set(v___x_967_, 1, v___x_966_);
        v___x_968_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_968_, 0, v___x_967_);
        return v___x_968_;
    }
}
pub unsafe fn l_Lean_Expr_and_x3f___boxed(mut v_p_969_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_970_: *mut LeanObject = core::ptr::null_mut();
    v_res_970_ = l_Lean_Expr_and_x3f(v_p_969_);
    lean_dec_ref(v_p_969_);
    return v_res_970_;
}
pub unsafe fn l_Lean_Expr_heq_x3f(mut v_p_974_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: u8 = 0;
    v___x_975_ = l_Lean_Expr_heq_x3f___closed__1;
    v___x_976_ = lean_unsigned_to_nat(4);
    v___x_977_ = l_Lean_Expr_isAppOfArity(v_p_974_, v___x_975_, v___x_976_);
    if v___x_977_ == 0 {
        let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
        v___x_978_ = lean_box(0);
        return v___x_978_;
    } else {
        let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
        v___x_979_ = l_Lean_Expr_appFn_x21(v_p_974_);
        v___x_980_ = l_Lean_Expr_appFn_x21(v___x_979_);
        v___x_981_ = l_Lean_Expr_appFn_x21(v___x_980_);
        v___x_982_ = l_Lean_Expr_appArg_x21(v___x_981_);
        lean_dec_ref(v___x_981_);
        v___x_983_ = l_Lean_Expr_appArg_x21(v___x_980_);
        lean_dec_ref(v___x_980_);
        v___x_984_ = l_Lean_Expr_appArg_x21(v___x_979_);
        lean_dec_ref(v___x_979_);
        v___x_985_ = l_Lean_Expr_appArg_x21(v_p_974_);
        v___x_986_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_986_, 0, v___x_984_);
        lean_ctor_set(v___x_986_, 1, v___x_985_);
        v___x_987_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_987_, 0, v___x_983_);
        lean_ctor_set(v___x_987_, 1, v___x_986_);
        v___x_988_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_988_, 0, v___x_982_);
        lean_ctor_set(v___x_988_, 1, v___x_987_);
        v___x_989_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_989_, 0, v___x_988_);
        return v___x_989_;
    }
}
pub unsafe fn l_Lean_Expr_heq_x3f___boxed(mut v_p_990_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_991_: *mut LeanObject = core::ptr::null_mut();
    v_res_991_ = l_Lean_Expr_heq_x3f(v_p_990_);
    lean_dec_ref(v_p_990_);
    return v_res_991_;
}
pub unsafe fn l_Lean_Expr_natAdd_x3f(mut v_e_997_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: u8 = 0;
    v___x_998_ = l_Lean_Expr_natAdd_x3f___closed__2;
    v___x_999_ = lean_unsigned_to_nat(2);
    v___x_1000_ = l_Lean_Expr_isAppOfArity(v_e_997_, v___x_998_, v___x_999_);
    if v___x_1000_ == 0 {
        let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
        v___x_1001_ = lean_box(0);
        return v___x_1001_;
    } else {
        let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
        v___x_1002_ = l_Lean_Expr_appFn_x21(v_e_997_);
        v___x_1003_ = l_Lean_Expr_appArg_x21(v___x_1002_);
        lean_dec_ref(v___x_1002_);
        v___x_1004_ = l_Lean_Expr_appArg_x21(v_e_997_);
        v___x_1005_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1005_, 0, v___x_1003_);
        lean_ctor_set(v___x_1005_, 1, v___x_1004_);
        v___x_1006_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1006_, 0, v___x_1005_);
        return v___x_1006_;
    }
}
pub unsafe fn l_Lean_Expr_natAdd_x3f___boxed(mut v_e_1007_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1008_: *mut LeanObject = core::ptr::null_mut();
    v_res_1008_ = l_Lean_Expr_natAdd_x3f(v_e_1007_);
    lean_dec_ref(v_e_1007_);
    return v_res_1008_;
}
pub unsafe fn l_Lean_Expr_arrow_x3f(mut v_x_1009_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_1009_) == 7 {
        let mut v_binderType_1010_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_1011_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1012_: u8 = 0;
        v_binderType_1010_ = lean_ctor_get(v_x_1009_, 1);
        v_body_1011_ = lean_ctor_get(v_x_1009_, 2);
        v___x_1012_ = l_Lean_Expr_hasLooseBVars(v_body_1011_);
        if v___x_1012_ == 0 {
            let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_body_1011_);
            lean_inc_ref(v_binderType_1010_);
            v___x_1013_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_1013_, 0, v_binderType_1010_);
            lean_ctor_set(v___x_1013_, 1, v_body_1011_);
            v___x_1014_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_1014_, 0, v___x_1013_);
            return v___x_1014_;
        } else {
            let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
            v___x_1015_ = lean_box(0);
            return v___x_1015_;
        }
    } else {
        let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
        v___x_1016_ = lean_box(0);
        return v___x_1016_;
    }
}
pub unsafe fn l_Lean_Expr_arrow_x3f___boxed(mut v_x_1017_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1018_: *mut LeanObject = core::ptr::null_mut();
    v_res_1018_ = l_Lean_Expr_arrow_x3f(v_x_1017_);
    lean_dec_ref(v_x_1017_);
    return v_res_1018_;
}
pub unsafe fn l_Lean_Expr_isEq(mut v_e_1019_: *mut LeanObject) -> u8 {
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: u8 = 0;
    v___x_1020_ = l_Lean_Expr_eq_x3f___closed__1;
    v___x_1021_ = lean_unsigned_to_nat(3);
    v___x_1022_ = l_Lean_Expr_isAppOfArity(v_e_1019_, v___x_1020_, v___x_1021_);
    return v___x_1022_;
}
pub unsafe fn l_Lean_Expr_isEq___boxed(mut v_e_1023_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1024_: u8 = 0;
    let mut v_r_1025_: *mut LeanObject = core::ptr::null_mut();
    v_res_1024_ = l_Lean_Expr_isEq(v_e_1023_);
    lean_dec_ref(v_e_1023_);
    v_r_1025_ = lean_box((v_res_1024_) as usize);
    return v_r_1025_;
}
pub unsafe fn l_Lean_Expr_isHEq(mut v_e_1026_: *mut LeanObject) -> u8 {
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: u8 = 0;
    v___x_1027_ = l_Lean_Expr_heq_x3f___closed__1;
    v___x_1028_ = lean_unsigned_to_nat(4);
    v___x_1029_ = l_Lean_Expr_isAppOfArity(v_e_1026_, v___x_1027_, v___x_1028_);
    return v___x_1029_;
}
pub unsafe fn l_Lean_Expr_isHEq___boxed(mut v_e_1030_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1031_: u8 = 0;
    let mut v_r_1032_: *mut LeanObject = core::ptr::null_mut();
    v_res_1031_ = l_Lean_Expr_isHEq(v_e_1030_);
    lean_dec_ref(v_e_1030_);
    v_r_1032_ = lean_box((v_res_1031_) as usize);
    return v_r_1032_;
}
pub unsafe fn l_Lean_Expr_isIte(mut v_e_1036_: *mut LeanObject) -> u8 {
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: u8 = 0;
    v___x_1037_ = l_Lean_Expr_isIte___closed__1;
    v___x_1038_ = lean_unsigned_to_nat(5);
    v___x_1039_ = l_Lean_Expr_isAppOfArity(v_e_1036_, v___x_1037_, v___x_1038_);
    return v___x_1039_;
}
pub unsafe fn l_Lean_Expr_isIte___boxed(mut v_e_1040_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1041_: u8 = 0;
    let mut v_r_1042_: *mut LeanObject = core::ptr::null_mut();
    v_res_1041_ = l_Lean_Expr_isIte(v_e_1040_);
    lean_dec_ref(v_e_1040_);
    v_r_1042_ = lean_box((v_res_1041_) as usize);
    return v_r_1042_;
}
pub unsafe fn l_Lean_Expr_isDIte(mut v_e_1046_: *mut LeanObject) -> u8 {
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: u8 = 0;
    v___x_1047_ = l_Lean_Expr_isDIte___closed__1;
    v___x_1048_ = lean_unsigned_to_nat(5);
    v___x_1049_ = l_Lean_Expr_isAppOfArity(v_e_1046_, v___x_1047_, v___x_1048_);
    return v___x_1049_;
}
pub unsafe fn l_Lean_Expr_isDIte___boxed(mut v_e_1050_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1051_: u8 = 0;
    let mut v_r_1052_: *mut LeanObject = core::ptr::null_mut();
    v_res_1051_ = l_Lean_Expr_isDIte(v_e_1050_);
    lean_dec_ref(v_e_1050_);
    v_r_1052_ = lean_box((v_res_1051_) as usize);
    return v_r_1052_;
}
pub unsafe fn l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop(
    mut v_e_1062_: *mut LeanObject,
    mut v_acc_1063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: u8 = 0;
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: u8 = 0;
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1064_ =
                    l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__2;
                v___x_1065_ = lean_unsigned_to_nat(1);
                v___x_1066_ = l_Lean_Expr_isAppOfArity_x27(v_e_1062_, v___x_1064_, v___x_1065_);
                if v___x_1066_ == 0 {
                    v___x_1067_ =
                        l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__4;
                    v___x_1068_ = lean_unsigned_to_nat(3);
                    v___x_1069_ = l_Lean_Expr_isAppOfArity_x27(v_e_1062_, v___x_1067_, v___x_1068_);
                    if v___x_1069_ == 0 {
                        lean_dec(v_acc_1063_);
                        lean_dec_ref(v_e_1062_);
                        v___x_1070_ = lean_box(0);
                        return v___x_1070_;
                    } else {
                        v___x_1071_ = l_Lean_Expr_appArg_x21_x27(v_e_1062_);
                        v___x_1072_ = l_Lean_Expr_appFn_x21_x27(v_e_1062_);
                        lean_dec_ref(v_e_1062_);
                        v___x_1073_ = l_Lean_Expr_appArg_x21_x27(v___x_1072_);
                        lean_dec_ref(v___x_1072_);
                        v___x_1074_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_1074_, 0, v___x_1073_);
                        lean_ctor_set(v___x_1074_, 1, v_acc_1063_);
                        v_e_1062_ = v___x_1071_;
                        v_acc_1063_ = v___x_1074_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_1076_ = l_Lean_Expr_appArg_x21_x27(v_e_1062_);
                    lean_dec_ref(v_e_1062_);
                    v___x_1077_ = l_List_reverse___redArg(v_acc_1063_);
                    v___x_1078_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1078_, 0, v___x_1076_);
                    lean_ctor_set(v___x_1078_, 1, v___x_1077_);
                    v___x_1079_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1079_, 0, v___x_1078_);
                    return v___x_1079_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_listLit_x3f(mut v_e_1080_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    v___x_1081_ = lean_box(0);
    v___x_1082_ =
        l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop(v_e_1080_, v___x_1081_);
    return v___x_1082_;
}
pub unsafe fn l_Lean_Expr_arrayLit_x3f(mut v_e_1087_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: u8 = 0;
    v___x_1088_ = l_Lean_Expr_arrayLit_x3f___closed__1;
    v___x_1089_ = lean_unsigned_to_nat(2);
    v___x_1090_ = l_Lean_Expr_isAppOfArity_x27(v_e_1087_, v___x_1088_, v___x_1089_);
    if v___x_1090_ == 0 {
        let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
        v___x_1091_ = lean_box(0);
        return v___x_1091_;
    } else {
        let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
        v___x_1092_ = l_Lean_Expr_appArg_x21_x27(v_e_1087_);
        v___x_1093_ = l_Lean_Expr_listLit_x3f(v___x_1092_);
        return v___x_1093_;
    }
}
pub unsafe fn l_Lean_Expr_arrayLit_x3f___boxed(mut v_e_1094_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1095_: *mut LeanObject = core::ptr::null_mut();
    v_res_1095_ = l_Lean_Expr_arrayLit_x3f(v_e_1094_);
    lean_dec_ref(v_e_1094_);
    return v_res_1095_;
}
pub unsafe fn l_Lean_Expr_prod_x3f(mut v_e_1099_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: u8 = 0;
    v___x_1100_ = l_Lean_Expr_prod_x3f___closed__1;
    v___x_1101_ = lean_unsigned_to_nat(2);
    v___x_1102_ = l_Lean_Expr_isAppOfArity(v_e_1099_, v___x_1100_, v___x_1101_);
    if v___x_1102_ == 0 {
        let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
        v___x_1103_ = lean_box(0);
        return v___x_1103_;
    } else {
        let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
        v___x_1104_ = l_Lean_Expr_appFn_x21(v_e_1099_);
        v___x_1105_ = l_Lean_Expr_appArg_x21(v___x_1104_);
        lean_dec_ref(v___x_1104_);
        v___x_1106_ = l_Lean_Expr_appArg_x21(v_e_1099_);
        v___x_1107_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1107_, 0, v___x_1105_);
        lean_ctor_set(v___x_1107_, 1, v___x_1106_);
        v___x_1108_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1108_, 0, v___x_1107_);
        return v___x_1108_;
    }
}
pub unsafe fn l_Lean_Expr_prod_x3f___boxed(mut v_e_1109_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1110_: *mut LeanObject = core::ptr::null_mut();
    v_res_1110_ = l_Lean_Expr_prod_x3f(v_e_1109_);
    lean_dec_ref(v_e_1109_);
    return v_res_1110_;
}
pub unsafe fn l_Lean_Expr_name_x3f(mut v_x_1124_: *mut LeanObject) -> *mut LeanObject {
    let mut v_declName_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: u8 = 0;
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: u8 = 0;
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: u8 = 0;
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1158_: u8 = 0;
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1163_: u8 = 0;
    let mut v_declName_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: u8 = 0;
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: u8 = 0;
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: u8 = 0;
    let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: u8 = 0;
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1190_: u8 = 0;
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1195_: u8 = 0;
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1208_: u8 = 0;
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1213_: u8 = 0;
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: u8 = 0;
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: u8 = 0;
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: u8 = 0;
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1246_: u8 = 0;
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1251_: u8 = 0;
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: u8 = 0;
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: u8 = 0;
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: u8 = 0;
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1291_: u8 = 0;
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1296_: u8 = 0;
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: u8 = 0;
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: u8 = 0;
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: u8 = 0;
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1341_: u8 = 0;
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1346_: u8 = 0;
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: u8 = 0;
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: u8 = 0;
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: u8 = 0;
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1396_: u8 = 0;
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1401_: u8 = 0;
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: u8 = 0;
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: u8 = 0;
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: u8 = 0;
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1456_: u8 = 0;
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1461_: u8 = 0;
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: u8 = 0;
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: u8 = 0;
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: u8 = 0;
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1521_: u8 = 0;
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1526_: u8 = 0;
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: u8 = 0;
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: u8 = 0;
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: u8 = 0;
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1575_: u8 = 0;
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1580_: u8 = 0;
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match lean_obj_tag(v_x_1124_) {
                    4 => {
                        v_declName_1125_ = lean_ctor_get(v_x_1124_, 0);
                        lean_inc(v_declName_1125_);
                        lean_dec_ref_known(v_x_1124_, 2);
                        if lean_obj_tag(v_declName_1125_) == 1 {
                            v_pre_1126_ = lean_ctor_get(v_declName_1125_, 0);
                            lean_inc(v_pre_1126_);
                            if lean_obj_tag(v_pre_1126_) == 1 {
                                v_pre_1127_ = lean_ctor_get(v_pre_1126_, 0);
                                lean_inc(v_pre_1127_);
                                if lean_obj_tag(v_pre_1127_) == 1 {
                                    v_pre_1128_ = lean_ctor_get(v_pre_1127_, 0);
                                    lean_inc(v_pre_1128_);
                                    if lean_obj_tag(v_pre_1128_) == 0 {
                                        v_str_1129_ = lean_ctor_get(v_declName_1125_, 1);
                                        lean_inc_ref(v_str_1129_);
                                        lean_dec_ref_known(v_declName_1125_, 2);
                                        v_str_1130_ = lean_ctor_get(v_pre_1126_, 1);
                                        lean_inc_ref(v_str_1130_);
                                        lean_dec_ref_known(v_pre_1126_, 2);
                                        v_str_1131_ = lean_ctor_get(v_pre_1127_, 1);
                                        lean_inc_ref(v_str_1131_);
                                        lean_dec_ref_known(v_pre_1127_, 2);
                                        v___x_1132_ = l_Lean_Expr_name_x3f___closed__0;
                                        v___x_1133_ = lean_string_dec_eq(v_str_1131_, v___x_1132_);
                                        lean_dec_ref(v_str_1131_);
                                        if v___x_1133_ == 0 {
                                            lean_dec_ref(v_str_1130_);
                                            lean_dec_ref(v_str_1129_);
                                            v___x_1134_ = lean_box(0);
                                            return v___x_1134_;
                                        } else {
                                            v___x_1135_ = l_Lean_Expr_name_x3f___closed__1;
                                            v___x_1136_ =
                                                lean_string_dec_eq(v_str_1130_, v___x_1135_);
                                            lean_dec_ref(v_str_1130_);
                                            if v___x_1136_ == 0 {
                                                lean_dec_ref(v_str_1129_);
                                                v___x_1137_ = lean_box(0);
                                                return v___x_1137_;
                                            } else {
                                                v___x_1138_ = l_Lean_Expr_name_x3f___closed__2;
                                                v___x_1139_ =
                                                    lean_string_dec_eq(v_str_1129_, v___x_1138_);
                                                lean_dec_ref(v_str_1129_);
                                                if v___x_1139_ == 0 {
                                                    v___x_1140_ = lean_box(0);
                                                    return v___x_1140_;
                                                } else {
                                                    v___x_1141_ = lean_alloc_ctor(1, 1, (0) as u32);
                                                    lean_ctor_set(v___x_1141_, 0, v_pre_1128_);
                                                    return v___x_1141_;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref_known(v_pre_1127_, 2);
                                        lean_dec(v_pre_1128_);
                                        lean_dec_ref_known(v_pre_1126_, 2);
                                        lean_dec_ref_known(v_declName_1125_, 2);
                                        v___x_1142_ = lean_box(0);
                                        return v___x_1142_;
                                    }
                                } else {
                                    lean_dec(v_pre_1127_);
                                    lean_dec_ref_known(v_pre_1126_, 2);
                                    lean_dec_ref_known(v_declName_1125_, 2);
                                    v___x_1143_ = lean_box(0);
                                    return v___x_1143_;
                                }
                            } else {
                                lean_dec(v_pre_1126_);
                                lean_dec_ref_known(v_declName_1125_, 2);
                                v___x_1144_ = lean_box(0);
                                return v___x_1144_;
                            }
                        } else {
                            lean_dec(v_declName_1125_);
                            v___x_1145_ = lean_box(0);
                            return v___x_1145_;
                        }
                    }
                    5 => {
                        v_fn_1146_ = lean_ctor_get(v_x_1124_, 0);
                        match lean_obj_tag(v_fn_1146_) {
                            5 => {
                                lean_inc_ref(v_fn_1146_);
                                v_arg_1147_ = lean_ctor_get(v_x_1124_, 1);
                                lean_inc_ref(v_arg_1147_);
                                lean_dec_ref_known(v_x_1124_, 2);
                                v_fn_1148_ = lean_ctor_get(v_fn_1146_, 0);
                                lean_inc_ref(v_fn_1148_);
                                v_arg_1149_ = lean_ctor_get(v_fn_1146_, 1);
                                lean_inc_ref(v_arg_1149_);
                                lean_dec_ref_known(v_fn_1146_, 2);
                                match lean_obj_tag(v_fn_1148_) {
                                    4 => {
                                        v_declName_1164_ = lean_ctor_get(v_fn_1148_, 0);
                                        lean_inc(v_declName_1164_);
                                        lean_dec_ref_known(v_fn_1148_, 2);
                                        if lean_obj_tag(v_declName_1164_) == 1 {
                                            v_pre_1165_ = lean_ctor_get(v_declName_1164_, 0);
                                            lean_inc(v_pre_1165_);
                                            if lean_obj_tag(v_pre_1165_) == 1 {
                                                v_pre_1166_ = lean_ctor_get(v_pre_1165_, 0);
                                                lean_inc(v_pre_1166_);
                                                if lean_obj_tag(v_pre_1166_) == 1 {
                                                    v_pre_1167_ = lean_ctor_get(v_pre_1166_, 0);
                                                    if lean_obj_tag(v_pre_1167_) == 0 {
                                                        v_str_1168_ =
                                                            lean_ctor_get(v_declName_1164_, 1);
                                                        lean_inc_ref(v_str_1168_);
                                                        lean_dec_ref_known(v_declName_1164_, 2);
                                                        v_str_1169_ = lean_ctor_get(v_pre_1165_, 1);
                                                        lean_inc_ref(v_str_1169_);
                                                        lean_dec_ref_known(v_pre_1165_, 2);
                                                        v_str_1170_ = lean_ctor_get(v_pre_1166_, 1);
                                                        lean_inc_ref(v_str_1170_);
                                                        lean_dec_ref_known(v_pre_1166_, 2);
                                                        v___x_1171_ =
                                                            l_Lean_Expr_name_x3f___closed__0;
                                                        v___x_1172_ = lean_string_dec_eq(
                                                            v_str_1170_,
                                                            v___x_1171_,
                                                        );
                                                        lean_dec_ref(v_str_1170_);
                                                        if v___x_1172_ == 0 {
                                                            lean_dec_ref(v_str_1169_);
                                                            lean_dec_ref(v_str_1168_);
                                                            lean_dec_ref(v_arg_1149_);
                                                            lean_dec_ref(v_arg_1147_);
                                                            v___x_1173_ = lean_box(0);
                                                            return v___x_1173_;
                                                        } else {
                                                            v___x_1174_ =
                                                                l_Lean_Expr_name_x3f___closed__1;
                                                            v___x_1175_ = lean_string_dec_eq(
                                                                v_str_1169_,
                                                                v___x_1174_,
                                                            );
                                                            lean_dec_ref(v_str_1169_);
                                                            if v___x_1175_ == 0 {
                                                                lean_dec_ref(v_str_1168_);
                                                                lean_dec_ref(v_arg_1149_);
                                                                lean_dec_ref(v_arg_1147_);
                                                                v___x_1176_ = lean_box(0);
                                                                return v___x_1176_;
                                                            } else {
                                                                v___x_1177_ = l_Lean_Expr_name_x3f___closed__3;
                                                                v___x_1178_ = lean_string_dec_eq(
                                                                    v_str_1168_,
                                                                    v___x_1177_,
                                                                );
                                                                if v___x_1178_ == 0 {
                                                                    v___x_1179_ = l_Lean_Expr_name_x3f___closed__4;
                                                                    v___x_1180_ =
                                                                        lean_string_dec_eq(
                                                                            v_str_1168_,
                                                                            v___x_1179_,
                                                                        );
                                                                    if v___x_1180_ == 0 {
                                                                        v___x_1181_ = l_Lean_Expr_name_x3f___closed__5;
                                                                        v___x_1182_ =
                                                                            lean_string_dec_eq(
                                                                                v_str_1168_,
                                                                                v___x_1181_,
                                                                            );
                                                                        lean_dec_ref(v_str_1168_);
                                                                        if v___x_1182_ == 0 {
                                                                            lean_dec_ref(
                                                                                v_arg_1149_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_1147_,
                                                                            );
                                                                            v___x_1183_ =
                                                                                lean_box(0);
                                                                            return v___x_1183_;
                                                                        } else {
                                                                            if lean_obj_tag(
                                                                                v_arg_1149_,
                                                                            ) == 9
                                                                            {
                                                                                v_a_1184_ =
                                                                                    lean_ctor_get(
                                                                                        v_arg_1149_,
                                                                                        0,
                                                                                    );
                                                                                lean_inc_ref(
                                                                                    v_a_1184_,
                                                                                );
                                                                                lean_dec_ref_known(
                                                                                    v_arg_1149_,
                                                                                    1,
                                                                                );
                                                                                if lean_obj_tag(
                                                                                    v_a_1184_,
                                                                                ) == 1
                                                                                {
                                                                                    if lean_obj_tag(
                                                                                        v_arg_1147_,
                                                                                    ) == 9
                                                                                    {
                                                                                        v_a_1185_ = lean_ctor_get(v_arg_1147_, 0);
                                                                                        lean_inc_ref(v_a_1185_);
                                                                                        lean_dec_ref_known(v_arg_1147_, 1);
                                                                                        if lean_obj_tag(v_a_1185_) == 1 {
v_val_1186_ = lean_ctor_get(v_a_1184_, 0);
lean_inc_ref(v_val_1186_);
lean_dec_ref_known(v_a_1184_, 1);
v_val_1187_ = lean_ctor_get(v_a_1185_, 0);
v_isSharedCheck_1195_ = (!lean_is_exclusive(v_a_1185_)) as u8;
if v_isSharedCheck_1195_ == 0 {
v___x_1189_ = v_a_1185_;
v_isShared_1190_ = v_isSharedCheck_1195_;
state = 4; continue;
} else {
lean_inc(v_val_1187_);
lean_dec(v_a_1185_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1195_;
state = 4; continue;
}
} else {
lean_dec_ref(v_a_1185_);
lean_dec_ref_known(v_a_1184_, 1);
v___x_1196_ = lean_box(0);
return v___x_1196_;
}
                                                                                    } else {
                                                                                        lean_dec_ref_known(v_a_1184_, 1);
                                                                                        lean_dec_ref(v_arg_1147_);
                                                                                        v___x_1197_ = lean_box(0);
                                                                                        return v___x_1197_;
                                                                                    }
                                                                                } else {
                                                                                    lean_dec_ref(
                                                                                        v_a_1184_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_arg_1147_,
                                                                                    );
                                                                                    v___x_1198_ =
                                                                                        lean_box(0);
                                                                                    return v___x_1198_;
                                                                                }
                                                                            } else {
                                                                                lean_dec_ref(
                                                                                    v_arg_1149_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_1147_,
                                                                                );
                                                                                v___x_1199_ =
                                                                                    lean_box(0);
                                                                                return v___x_1199_;
                                                                            }
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref(v_str_1168_);
                                                                        lean_inc_ref(v_arg_1147_);
                                                                        v___x_1200_ = l_Lean_Expr_rawNatLit_x3f(v_arg_1147_);
                                                                        if lean_obj_tag(v___x_1200_)
                                                                            == 0
                                                                        {
                                                                            v___x_1201_ =
                                                                                l_Lean_Expr_nat_x3f(
                                                                                    v_arg_1147_,
                                                                                );
                                                                            v___y_1151_ =
                                                                                v___x_1201_;
                                                                            state = 1;
                                                                            continue;
                                                                        } else {
                                                                            lean_dec_ref(
                                                                                v_arg_1147_,
                                                                            );
                                                                            v___y_1151_ =
                                                                                v___x_1200_;
                                                                            state = 1;
                                                                            continue;
                                                                        }
                                                                    }
                                                                } else {
                                                                    lean_dec_ref(v_str_1168_);
                                                                    if lean_obj_tag(v_arg_1147_)
                                                                        == 9
                                                                    {
                                                                        v_a_1202_ = lean_ctor_get(
                                                                            v_arg_1147_,
                                                                            0,
                                                                        );
                                                                        lean_inc_ref(v_a_1202_);
                                                                        lean_dec_ref_known(
                                                                            v_arg_1147_,
                                                                            1,
                                                                        );
                                                                        if lean_obj_tag(v_a_1202_)
                                                                            == 1
                                                                        {
                                                                            v_val_1203_ =
                                                                                lean_ctor_get(
                                                                                    v_a_1202_, 0,
                                                                                );
                                                                            lean_inc_ref(
                                                                                v_val_1203_,
                                                                            );
                                                                            lean_dec_ref_known(
                                                                                v_a_1202_, 1,
                                                                            );
                                                                            v___x_1204_ = l_Lean_Expr_name_x3f(v_arg_1149_);
                                                                            if lean_obj_tag(
                                                                                v___x_1204_,
                                                                            ) == 0
                                                                            {
                                                                                lean_dec_ref(
                                                                                    v_val_1203_,
                                                                                );
                                                                                return v___x_1204_;
                                                                            } else {
                                                                                v_val_1205_ =
                                                                                    lean_ctor_get(
                                                                                        v___x_1204_,
                                                                                        0,
                                                                                    );
                                                                                v_isSharedCheck_1213_ = (!lean_is_exclusive(v___x_1204_)) as u8;
                                                                                if v_isSharedCheck_1213_ == 0 {
v___x_1207_ = v___x_1204_;
v_isShared_1208_ = v_isSharedCheck_1213_;
state = 6; continue;
} else {
lean_inc(v_val_1205_);
lean_dec(v___x_1204_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1213_;
state = 6; continue;
}
                                                                            }
                                                                        } else {
                                                                            lean_dec_ref(v_a_1202_);
                                                                            lean_dec_ref(
                                                                                v_arg_1149_,
                                                                            );
                                                                            v___x_1214_ =
                                                                                lean_box(0);
                                                                            return v___x_1214_;
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref(v_arg_1149_);
                                                                        lean_dec_ref(v_arg_1147_);
                                                                        v___x_1215_ = lean_box(0);
                                                                        return v___x_1215_;
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    } else {
                                                        lean_dec_ref_known(v_pre_1166_, 2);
                                                        lean_dec_ref_known(v_pre_1165_, 2);
                                                        lean_dec_ref_known(v_declName_1164_, 2);
                                                        lean_dec_ref(v_arg_1149_);
                                                        lean_dec_ref(v_arg_1147_);
                                                        v___x_1216_ = lean_box(0);
                                                        return v___x_1216_;
                                                    }
                                                } else {
                                                    lean_dec_ref_known(v_pre_1165_, 2);
                                                    lean_dec(v_pre_1166_);
                                                    lean_dec_ref_known(v_declName_1164_, 2);
                                                    lean_dec_ref(v_arg_1149_);
                                                    lean_dec_ref(v_arg_1147_);
                                                    v___x_1217_ = lean_box(0);
                                                    return v___x_1217_;
                                                }
                                            } else {
                                                lean_dec(v_pre_1165_);
                                                lean_dec_ref_known(v_declName_1164_, 2);
                                                lean_dec_ref(v_arg_1149_);
                                                lean_dec_ref(v_arg_1147_);
                                                v___x_1218_ = lean_box(0);
                                                return v___x_1218_;
                                            }
                                        } else {
                                            lean_dec(v_declName_1164_);
                                            lean_dec_ref(v_arg_1149_);
                                            lean_dec_ref(v_arg_1147_);
                                            v___x_1219_ = lean_box(0);
                                            return v___x_1219_;
                                        }
                                    }
                                    5 => {
                                        v_fn_1220_ = lean_ctor_get(v_fn_1148_, 0);
                                        match lean_obj_tag(v_fn_1220_) {
                                            4 => {
                                                v_declName_1221_ = lean_ctor_get(v_fn_1220_, 0);
                                                lean_inc(v_declName_1221_);
                                                if lean_obj_tag(v_declName_1221_) == 1 {
                                                    v_pre_1222_ =
                                                        lean_ctor_get(v_declName_1221_, 0);
                                                    lean_inc(v_pre_1222_);
                                                    if lean_obj_tag(v_pre_1222_) == 1 {
                                                        v_pre_1223_ = lean_ctor_get(v_pre_1222_, 0);
                                                        lean_inc(v_pre_1223_);
                                                        if lean_obj_tag(v_pre_1223_) == 1 {
                                                            v_pre_1224_ =
                                                                lean_ctor_get(v_pre_1223_, 0);
                                                            if lean_obj_tag(v_pre_1224_) == 0 {
                                                                v_arg_1225_ =
                                                                    lean_ctor_get(v_fn_1148_, 1);
                                                                lean_inc_ref(v_arg_1225_);
                                                                lean_dec_ref_known(v_fn_1148_, 2);
                                                                v_str_1226_ = lean_ctor_get(
                                                                    v_declName_1221_,
                                                                    1,
                                                                );
                                                                lean_inc_ref(v_str_1226_);
                                                                lean_dec_ref_known(
                                                                    v_declName_1221_,
                                                                    2,
                                                                );
                                                                v_str_1227_ =
                                                                    lean_ctor_get(v_pre_1222_, 1);
                                                                lean_inc_ref(v_str_1227_);
                                                                lean_dec_ref_known(v_pre_1222_, 2);
                                                                v_str_1228_ =
                                                                    lean_ctor_get(v_pre_1223_, 1);
                                                                lean_inc_ref(v_str_1228_);
                                                                lean_dec_ref_known(v_pre_1223_, 2);
                                                                v___x_1229_ = l_Lean_Expr_name_x3f___closed__0;
                                                                v___x_1230_ = lean_string_dec_eq(
                                                                    v_str_1228_,
                                                                    v___x_1229_,
                                                                );
                                                                lean_dec_ref(v_str_1228_);
                                                                if v___x_1230_ == 0 {
                                                                    lean_dec_ref(v_str_1227_);
                                                                    lean_dec_ref(v_str_1226_);
                                                                    lean_dec_ref(v_arg_1225_);
                                                                    lean_dec_ref(v_arg_1149_);
                                                                    lean_dec_ref(v_arg_1147_);
                                                                    v___x_1231_ = lean_box(0);
                                                                    return v___x_1231_;
                                                                } else {
                                                                    v___x_1232_ = l_Lean_Expr_name_x3f___closed__1;
                                                                    v___x_1233_ =
                                                                        lean_string_dec_eq(
                                                                            v_str_1227_,
                                                                            v___x_1232_,
                                                                        );
                                                                    lean_dec_ref(v_str_1227_);
                                                                    if v___x_1233_ == 0 {
                                                                        lean_dec_ref(v_str_1226_);
                                                                        lean_dec_ref(v_arg_1225_);
                                                                        lean_dec_ref(v_arg_1149_);
                                                                        lean_dec_ref(v_arg_1147_);
                                                                        v___x_1234_ = lean_box(0);
                                                                        return v___x_1234_;
                                                                    } else {
                                                                        v___x_1235_ = l_Lean_Expr_name_x3f___closed__6;
                                                                        v___x_1236_ =
                                                                            lean_string_dec_eq(
                                                                                v_str_1226_,
                                                                                v___x_1235_,
                                                                            );
                                                                        lean_dec_ref(v_str_1226_);
                                                                        if v___x_1236_ == 0 {
                                                                            lean_dec_ref(
                                                                                v_arg_1225_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_1149_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_1147_,
                                                                            );
                                                                            v___x_1237_ =
                                                                                lean_box(0);
                                                                            return v___x_1237_;
                                                                        } else {
                                                                            if lean_obj_tag(
                                                                                v_arg_1225_,
                                                                            ) == 9
                                                                            {
                                                                                v_a_1238_ =
                                                                                    lean_ctor_get(
                                                                                        v_arg_1225_,
                                                                                        0,
                                                                                    );
                                                                                lean_inc_ref(
                                                                                    v_a_1238_,
                                                                                );
                                                                                lean_dec_ref_known(
                                                                                    v_arg_1225_,
                                                                                    1,
                                                                                );
                                                                                if lean_obj_tag(
                                                                                    v_a_1238_,
                                                                                ) == 1
                                                                                {
                                                                                    if lean_obj_tag(
                                                                                        v_arg_1149_,
                                                                                    ) == 9
                                                                                    {
                                                                                        v_a_1239_ = lean_ctor_get(v_arg_1149_, 0);
                                                                                        lean_inc_ref(v_a_1239_);
                                                                                        lean_dec_ref_known(v_arg_1149_, 1);
                                                                                        if lean_obj_tag(v_a_1239_) == 1 {
if lean_obj_tag(v_arg_1147_) == 9 {
v_a_1240_ = lean_ctor_get(v_arg_1147_, 0);
lean_inc_ref(v_a_1240_);
lean_dec_ref_known(v_arg_1147_, 1);
if lean_obj_tag(v_a_1240_) == 1 {
v_val_1241_ = lean_ctor_get(v_a_1238_, 0);
lean_inc_ref(v_val_1241_);
lean_dec_ref_known(v_a_1238_, 1);
v_val_1242_ = lean_ctor_get(v_a_1239_, 0);
lean_inc_ref(v_val_1242_);
lean_dec_ref_known(v_a_1239_, 1);
v_val_1243_ = lean_ctor_get(v_a_1240_, 0);
v_isSharedCheck_1251_ = (!lean_is_exclusive(v_a_1240_)) as u8;
if v_isSharedCheck_1251_ == 0 {
v___x_1245_ = v_a_1240_;
v_isShared_1246_ = v_isSharedCheck_1251_;
state = 8; continue;
} else {
lean_inc(v_val_1243_);
lean_dec(v_a_1240_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1251_;
state = 8; continue;
}
} else {
lean_dec_ref(v_a_1240_);
lean_dec_ref_known(v_a_1239_, 1);
lean_dec_ref_known(v_a_1238_, 1);
v___x_1252_ = lean_box(0);
return v___x_1252_;
}
} else {
lean_dec_ref_known(v_a_1239_, 1);
lean_dec_ref_known(v_a_1238_, 1);
lean_dec_ref(v_arg_1147_);
v___x_1253_ = lean_box(0);
return v___x_1253_;
}
} else {
lean_dec_ref(v_a_1239_);
lean_dec_ref_known(v_a_1238_, 1);
lean_dec_ref(v_arg_1147_);
v___x_1254_ = lean_box(0);
return v___x_1254_;
}
                                                                                    } else {
                                                                                        lean_dec_ref_known(v_a_1238_, 1);
                                                                                        lean_dec_ref(v_arg_1149_);
                                                                                        lean_dec_ref(v_arg_1147_);
                                                                                        v___x_1255_ = lean_box(0);
                                                                                        return v___x_1255_;
                                                                                    }
                                                                                } else {
                                                                                    lean_dec_ref(
                                                                                        v_a_1238_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_arg_1149_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_arg_1147_,
                                                                                    );
                                                                                    v___x_1256_ =
                                                                                        lean_box(0);
                                                                                    return v___x_1256_;
                                                                                }
                                                                            } else {
                                                                                lean_dec_ref(
                                                                                    v_arg_1225_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_1149_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_1147_,
                                                                                );
                                                                                v___x_1257_ =
                                                                                    lean_box(0);
                                                                                return v___x_1257_;
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                lean_dec_ref_known(v_pre_1223_, 2);
                                                                lean_dec_ref_known(v_pre_1222_, 2);
                                                                lean_dec_ref_known(
                                                                    v_declName_1221_,
                                                                    2,
                                                                );
                                                                lean_dec_ref_known(v_fn_1148_, 2);
                                                                lean_dec_ref(v_arg_1149_);
                                                                lean_dec_ref(v_arg_1147_);
                                                                v___x_1258_ = lean_box(0);
                                                                return v___x_1258_;
                                                            }
                                                        } else {
                                                            lean_dec(v_pre_1223_);
                                                            lean_dec_ref_known(v_pre_1222_, 2);
                                                            lean_dec_ref_known(v_declName_1221_, 2);
                                                            lean_dec_ref_known(v_fn_1148_, 2);
                                                            lean_dec_ref(v_arg_1149_);
                                                            lean_dec_ref(v_arg_1147_);
                                                            v___x_1259_ = lean_box(0);
                                                            return v___x_1259_;
                                                        }
                                                    } else {
                                                        lean_dec_ref_known(v_declName_1221_, 2);
                                                        lean_dec(v_pre_1222_);
                                                        lean_dec_ref_known(v_fn_1148_, 2);
                                                        lean_dec_ref(v_arg_1149_);
                                                        lean_dec_ref(v_arg_1147_);
                                                        v___x_1260_ = lean_box(0);
                                                        return v___x_1260_;
                                                    }
                                                } else {
                                                    lean_dec(v_declName_1221_);
                                                    lean_dec_ref_known(v_fn_1148_, 2);
                                                    lean_dec_ref(v_arg_1149_);
                                                    lean_dec_ref(v_arg_1147_);
                                                    v___x_1261_ = lean_box(0);
                                                    return v___x_1261_;
                                                }
                                            }
                                            5 => {
                                                lean_inc_ref(v_fn_1220_);
                                                v_fn_1262_ = lean_ctor_get(v_fn_1220_, 0);
                                                match lean_obj_tag(v_fn_1262_) {
                                                    4 => {
                                                        v_declName_1263_ =
                                                            lean_ctor_get(v_fn_1262_, 0);
                                                        lean_inc(v_declName_1263_);
                                                        if lean_obj_tag(v_declName_1263_) == 1 {
                                                            v_pre_1264_ =
                                                                lean_ctor_get(v_declName_1263_, 0);
                                                            lean_inc(v_pre_1264_);
                                                            if lean_obj_tag(v_pre_1264_) == 1 {
                                                                v_pre_1265_ =
                                                                    lean_ctor_get(v_pre_1264_, 0);
                                                                lean_inc(v_pre_1265_);
                                                                if lean_obj_tag(v_pre_1265_) == 1 {
                                                                    v_pre_1266_ = lean_ctor_get(
                                                                        v_pre_1265_,
                                                                        0,
                                                                    );
                                                                    if lean_obj_tag(v_pre_1266_)
                                                                        == 0
                                                                    {
                                                                        v_arg_1267_ = lean_ctor_get(
                                                                            v_fn_1148_, 1,
                                                                        );
                                                                        lean_inc_ref(v_arg_1267_);
                                                                        lean_dec_ref_known(
                                                                            v_fn_1148_, 2,
                                                                        );
                                                                        v_arg_1268_ = lean_ctor_get(
                                                                            v_fn_1220_, 1,
                                                                        );
                                                                        lean_inc_ref(v_arg_1268_);
                                                                        lean_dec_ref_known(
                                                                            v_fn_1220_, 2,
                                                                        );
                                                                        v_str_1269_ = lean_ctor_get(
                                                                            v_declName_1263_,
                                                                            1,
                                                                        );
                                                                        lean_inc_ref(v_str_1269_);
                                                                        lean_dec_ref_known(
                                                                            v_declName_1263_,
                                                                            2,
                                                                        );
                                                                        v_str_1270_ = lean_ctor_get(
                                                                            v_pre_1264_,
                                                                            1,
                                                                        );
                                                                        lean_inc_ref(v_str_1270_);
                                                                        lean_dec_ref_known(
                                                                            v_pre_1264_,
                                                                            2,
                                                                        );
                                                                        v_str_1271_ = lean_ctor_get(
                                                                            v_pre_1265_,
                                                                            1,
                                                                        );
                                                                        lean_inc_ref(v_str_1271_);
                                                                        lean_dec_ref_known(
                                                                            v_pre_1265_,
                                                                            2,
                                                                        );
                                                                        v___x_1272_ = l_Lean_Expr_name_x3f___closed__0;
                                                                        v___x_1273_ =
                                                                            lean_string_dec_eq(
                                                                                v_str_1271_,
                                                                                v___x_1272_,
                                                                            );
                                                                        lean_dec_ref(v_str_1271_);
                                                                        if v___x_1273_ == 0 {
                                                                            lean_dec_ref(
                                                                                v_str_1270_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_str_1269_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_1268_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_1267_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_1149_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_1147_,
                                                                            );
                                                                            v___x_1274_ =
                                                                                lean_box(0);
                                                                            return v___x_1274_;
                                                                        } else {
                                                                            v___x_1275_ = l_Lean_Expr_name_x3f___closed__1;
                                                                            v___x_1276_ =
                                                                                lean_string_dec_eq(
                                                                                    v_str_1270_,
                                                                                    v___x_1275_,
                                                                                );
                                                                            lean_dec_ref(
                                                                                v_str_1270_,
                                                                            );
                                                                            if v___x_1276_ == 0 {
                                                                                lean_dec_ref(
                                                                                    v_str_1269_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_1268_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_1267_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_1149_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_1147_,
                                                                                );
                                                                                v___x_1277_ =
                                                                                    lean_box(0);
                                                                                return v___x_1277_;
                                                                            } else {
                                                                                v___x_1278_ = l_Lean_Expr_name_x3f___closed__7;
                                                                                v___x_1279_ = lean_string_dec_eq(v_str_1269_, v___x_1278_);
                                                                                lean_dec_ref(
                                                                                    v_str_1269_,
                                                                                );
                                                                                if v___x_1279_ == 0
                                                                                {
                                                                                    lean_dec_ref(
                                                                                        v_arg_1268_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_arg_1267_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_arg_1149_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_arg_1147_,
                                                                                    );
                                                                                    v___x_1280_ =
                                                                                        lean_box(0);
                                                                                    return v___x_1280_;
                                                                                } else {
                                                                                    if lean_obj_tag(
                                                                                        v_arg_1268_,
                                                                                    ) == 9
                                                                                    {
                                                                                        v_a_1281_ = lean_ctor_get(v_arg_1268_, 0);
                                                                                        lean_inc_ref(v_a_1281_);
                                                                                        lean_dec_ref_known(v_arg_1268_, 1);
                                                                                        if lean_obj_tag(v_a_1281_) == 1 {
if lean_obj_tag(v_arg_1267_) == 9 {
v_a_1282_ = lean_ctor_get(v_arg_1267_, 0);
lean_inc_ref(v_a_1282_);
lean_dec_ref_known(v_arg_1267_, 1);
if lean_obj_tag(v_a_1282_) == 1 {
if lean_obj_tag(v_arg_1149_) == 9 {
v_a_1283_ = lean_ctor_get(v_arg_1149_, 0);
lean_inc_ref(v_a_1283_);
lean_dec_ref_known(v_arg_1149_, 1);
if lean_obj_tag(v_a_1283_) == 1 {
if lean_obj_tag(v_arg_1147_) == 9 {
v_a_1284_ = lean_ctor_get(v_arg_1147_, 0);
lean_inc_ref(v_a_1284_);
lean_dec_ref_known(v_arg_1147_, 1);
if lean_obj_tag(v_a_1284_) == 1 {
v_val_1285_ = lean_ctor_get(v_a_1281_, 0);
lean_inc_ref(v_val_1285_);
lean_dec_ref_known(v_a_1281_, 1);
v_val_1286_ = lean_ctor_get(v_a_1282_, 0);
lean_inc_ref(v_val_1286_);
lean_dec_ref_known(v_a_1282_, 1);
v_val_1287_ = lean_ctor_get(v_a_1283_, 0);
lean_inc_ref(v_val_1287_);
lean_dec_ref_known(v_a_1283_, 1);
v_val_1288_ = lean_ctor_get(v_a_1284_, 0);
v_isSharedCheck_1296_ = (!lean_is_exclusive(v_a_1284_)) as u8;
if v_isSharedCheck_1296_ == 0 {
v___x_1290_ = v_a_1284_;
v_isShared_1291_ = v_isSharedCheck_1296_;
state = 10; continue;
} else {
lean_inc(v_val_1288_);
lean_dec(v_a_1284_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1296_;
state = 10; continue;
}
} else {
lean_dec_ref(v_a_1284_);
lean_dec_ref_known(v_a_1283_, 1);
lean_dec_ref_known(v_a_1282_, 1);
lean_dec_ref_known(v_a_1281_, 1);
v___x_1297_ = lean_box(0);
return v___x_1297_;
}
} else {
lean_dec_ref_known(v_a_1283_, 1);
lean_dec_ref_known(v_a_1282_, 1);
lean_dec_ref_known(v_a_1281_, 1);
lean_dec_ref(v_arg_1147_);
v___x_1298_ = lean_box(0);
return v___x_1298_;
}
} else {
lean_dec_ref(v_a_1283_);
lean_dec_ref_known(v_a_1282_, 1);
lean_dec_ref_known(v_a_1281_, 1);
lean_dec_ref(v_arg_1147_);
v___x_1299_ = lean_box(0);
return v___x_1299_;
}
} else {
lean_dec_ref_known(v_a_1282_, 1);
lean_dec_ref_known(v_a_1281_, 1);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1300_ = lean_box(0);
return v___x_1300_;
}
} else {
lean_dec_ref(v_a_1282_);
lean_dec_ref_known(v_a_1281_, 1);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1301_ = lean_box(0);
return v___x_1301_;
}
} else {
lean_dec_ref_known(v_a_1281_, 1);
lean_dec_ref(v_arg_1267_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1302_ = lean_box(0);
return v___x_1302_;
}
} else {
lean_dec_ref(v_a_1281_);
lean_dec_ref(v_arg_1267_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1303_ = lean_box(0);
return v___x_1303_;
}
                                                                                    } else {
                                                                                        lean_dec_ref(v_arg_1268_);
                                                                                        lean_dec_ref(v_arg_1267_);
                                                                                        lean_dec_ref(v_arg_1149_);
                                                                                        lean_dec_ref(v_arg_1147_);
                                                                                        v___x_1304_ = lean_box(0);
                                                                                        return v___x_1304_;
                                                                                    }
                                                                                }
                                                                            }
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref_known(
                                                                            v_pre_1265_,
                                                                            2,
                                                                        );
                                                                        lean_dec_ref_known(
                                                                            v_pre_1264_,
                                                                            2,
                                                                        );
                                                                        lean_dec_ref_known(
                                                                            v_declName_1263_,
                                                                            2,
                                                                        );
                                                                        lean_dec_ref_known(
                                                                            v_fn_1220_, 2,
                                                                        );
                                                                        lean_dec_ref_known(
                                                                            v_fn_1148_, 2,
                                                                        );
                                                                        lean_dec_ref(v_arg_1149_);
                                                                        lean_dec_ref(v_arg_1147_);
                                                                        v___x_1305_ = lean_box(0);
                                                                        return v___x_1305_;
                                                                    }
                                                                } else {
                                                                    lean_dec(v_pre_1265_);
                                                                    lean_dec_ref_known(
                                                                        v_pre_1264_,
                                                                        2,
                                                                    );
                                                                    lean_dec_ref_known(
                                                                        v_declName_1263_,
                                                                        2,
                                                                    );
                                                                    lean_dec_ref_known(
                                                                        v_fn_1220_, 2,
                                                                    );
                                                                    lean_dec_ref_known(
                                                                        v_fn_1148_, 2,
                                                                    );
                                                                    lean_dec_ref(v_arg_1149_);
                                                                    lean_dec_ref(v_arg_1147_);
                                                                    v___x_1306_ = lean_box(0);
                                                                    return v___x_1306_;
                                                                }
                                                            } else {
                                                                lean_dec_ref_known(
                                                                    v_declName_1263_,
                                                                    2,
                                                                );
                                                                lean_dec(v_pre_1264_);
                                                                lean_dec_ref_known(v_fn_1220_, 2);
                                                                lean_dec_ref_known(v_fn_1148_, 2);
                                                                lean_dec_ref(v_arg_1149_);
                                                                lean_dec_ref(v_arg_1147_);
                                                                v___x_1307_ = lean_box(0);
                                                                return v___x_1307_;
                                                            }
                                                        } else {
                                                            lean_dec(v_declName_1263_);
                                                            lean_dec_ref_known(v_fn_1220_, 2);
                                                            lean_dec_ref_known(v_fn_1148_, 2);
                                                            lean_dec_ref(v_arg_1149_);
                                                            lean_dec_ref(v_arg_1147_);
                                                            v___x_1308_ = lean_box(0);
                                                            return v___x_1308_;
                                                        }
                                                    }
                                                    5 => {
                                                        lean_inc_ref(v_fn_1262_);
                                                        v_fn_1309_ = lean_ctor_get(v_fn_1262_, 0);
                                                        match lean_obj_tag(v_fn_1309_) {
                                                            4 => {
                                                                v_declName_1310_ =
                                                                    lean_ctor_get(v_fn_1309_, 0);
                                                                lean_inc(v_declName_1310_);
                                                                if lean_obj_tag(v_declName_1310_)
                                                                    == 1
                                                                {
                                                                    v_pre_1311_ = lean_ctor_get(
                                                                        v_declName_1310_,
                                                                        0,
                                                                    );
                                                                    lean_inc(v_pre_1311_);
                                                                    if lean_obj_tag(v_pre_1311_)
                                                                        == 1
                                                                    {
                                                                        v_pre_1312_ = lean_ctor_get(
                                                                            v_pre_1311_,
                                                                            0,
                                                                        );
                                                                        lean_inc(v_pre_1312_);
                                                                        if lean_obj_tag(v_pre_1312_)
                                                                            == 1
                                                                        {
                                                                            v_pre_1313_ =
                                                                                lean_ctor_get(
                                                                                    v_pre_1312_,
                                                                                    0,
                                                                                );
                                                                            if lean_obj_tag(
                                                                                v_pre_1313_,
                                                                            ) == 0
                                                                            {
                                                                                v_arg_1314_ =
                                                                                    lean_ctor_get(
                                                                                        v_fn_1148_,
                                                                                        1,
                                                                                    );
                                                                                lean_inc_ref(
                                                                                    v_arg_1314_,
                                                                                );
                                                                                lean_dec_ref_known(
                                                                                    v_fn_1148_, 2,
                                                                                );
                                                                                v_arg_1315_ =
                                                                                    lean_ctor_get(
                                                                                        v_fn_1220_,
                                                                                        1,
                                                                                    );
                                                                                lean_inc_ref(
                                                                                    v_arg_1315_,
                                                                                );
                                                                                lean_dec_ref_known(
                                                                                    v_fn_1220_, 2,
                                                                                );
                                                                                v_arg_1316_ =
                                                                                    lean_ctor_get(
                                                                                        v_fn_1262_,
                                                                                        1,
                                                                                    );
                                                                                lean_inc_ref(
                                                                                    v_arg_1316_,
                                                                                );
                                                                                lean_dec_ref_known(
                                                                                    v_fn_1262_, 2,
                                                                                );
                                                                                v_str_1317_ = lean_ctor_get(v_declName_1310_, 1);
                                                                                lean_inc_ref(
                                                                                    v_str_1317_,
                                                                                );
                                                                                lean_dec_ref_known(v_declName_1310_, 2);
                                                                                v_str_1318_ =
                                                                                    lean_ctor_get(
                                                                                        v_pre_1311_,
                                                                                        1,
                                                                                    );
                                                                                lean_inc_ref(
                                                                                    v_str_1318_,
                                                                                );
                                                                                lean_dec_ref_known(
                                                                                    v_pre_1311_,
                                                                                    2,
                                                                                );
                                                                                v_str_1319_ =
                                                                                    lean_ctor_get(
                                                                                        v_pre_1312_,
                                                                                        1,
                                                                                    );
                                                                                lean_inc_ref(
                                                                                    v_str_1319_,
                                                                                );
                                                                                lean_dec_ref_known(
                                                                                    v_pre_1312_,
                                                                                    2,
                                                                                );
                                                                                v___x_1320_ = l_Lean_Expr_name_x3f___closed__0;
                                                                                v___x_1321_ = lean_string_dec_eq(v_str_1319_, v___x_1320_);
                                                                                lean_dec_ref(
                                                                                    v_str_1319_,
                                                                                );
                                                                                if v___x_1321_ == 0
                                                                                {
                                                                                    lean_dec_ref(
                                                                                        v_str_1318_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_str_1317_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_arg_1316_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_arg_1315_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_arg_1314_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_arg_1149_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_arg_1147_,
                                                                                    );
                                                                                    v___x_1322_ =
                                                                                        lean_box(0);
                                                                                    return v___x_1322_;
                                                                                } else {
                                                                                    v___x_1323_ = l_Lean_Expr_name_x3f___closed__1;
                                                                                    v___x_1324_ = lean_string_dec_eq(v_str_1318_, v___x_1323_);
                                                                                    lean_dec_ref(
                                                                                        v_str_1318_,
                                                                                    );
                                                                                    if v___x_1324_
                                                                                        == 0
                                                                                    {
                                                                                        lean_dec_ref(v_str_1317_);
                                                                                        lean_dec_ref(v_arg_1316_);
                                                                                        lean_dec_ref(v_arg_1315_);
                                                                                        lean_dec_ref(v_arg_1314_);
                                                                                        lean_dec_ref(v_arg_1149_);
                                                                                        lean_dec_ref(v_arg_1147_);
                                                                                        v___x_1325_ = lean_box(0);
                                                                                        return v___x_1325_;
                                                                                    } else {
                                                                                        v___x_1326_ = l_Lean_Expr_name_x3f___closed__8;
                                                                                        v___x_1327_ = lean_string_dec_eq(v_str_1317_, v___x_1326_);
                                                                                        lean_dec_ref(v_str_1317_);
                                                                                        if v___x_1327_ == 0 {
lean_dec_ref(v_arg_1316_);
lean_dec_ref(v_arg_1315_);
lean_dec_ref(v_arg_1314_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1328_ = lean_box(0);
return v___x_1328_;
} else {
if lean_obj_tag(v_arg_1316_) == 9 {
v_a_1329_ = lean_ctor_get(v_arg_1316_, 0);
lean_inc_ref(v_a_1329_);
lean_dec_ref_known(v_arg_1316_, 1);
if lean_obj_tag(v_a_1329_) == 1 {
if lean_obj_tag(v_arg_1315_) == 9 {
v_a_1330_ = lean_ctor_get(v_arg_1315_, 0);
lean_inc_ref(v_a_1330_);
lean_dec_ref_known(v_arg_1315_, 1);
if lean_obj_tag(v_a_1330_) == 1 {
if lean_obj_tag(v_arg_1314_) == 9 {
v_a_1331_ = lean_ctor_get(v_arg_1314_, 0);
lean_inc_ref(v_a_1331_);
lean_dec_ref_known(v_arg_1314_, 1);
if lean_obj_tag(v_a_1331_) == 1 {
if lean_obj_tag(v_arg_1149_) == 9 {
v_a_1332_ = lean_ctor_get(v_arg_1149_, 0);
lean_inc_ref(v_a_1332_);
lean_dec_ref_known(v_arg_1149_, 1);
if lean_obj_tag(v_a_1332_) == 1 {
if lean_obj_tag(v_arg_1147_) == 9 {
v_a_1333_ = lean_ctor_get(v_arg_1147_, 0);
lean_inc_ref(v_a_1333_);
lean_dec_ref_known(v_arg_1147_, 1);
if lean_obj_tag(v_a_1333_) == 1 {
v_val_1334_ = lean_ctor_get(v_a_1329_, 0);
lean_inc_ref(v_val_1334_);
lean_dec_ref_known(v_a_1329_, 1);
v_val_1335_ = lean_ctor_get(v_a_1330_, 0);
lean_inc_ref(v_val_1335_);
lean_dec_ref_known(v_a_1330_, 1);
v_val_1336_ = lean_ctor_get(v_a_1331_, 0);
lean_inc_ref(v_val_1336_);
lean_dec_ref_known(v_a_1331_, 1);
v_val_1337_ = lean_ctor_get(v_a_1332_, 0);
lean_inc_ref(v_val_1337_);
lean_dec_ref_known(v_a_1332_, 1);
v_val_1338_ = lean_ctor_get(v_a_1333_, 0);
v_isSharedCheck_1346_ = (!lean_is_exclusive(v_a_1333_)) as u8;
if v_isSharedCheck_1346_ == 0 {
v___x_1340_ = v_a_1333_;
v_isShared_1341_ = v_isSharedCheck_1346_;
state = 12; continue;
} else {
lean_inc(v_val_1338_);
lean_dec(v_a_1333_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1346_;
state = 12; continue;
}
} else {
lean_dec_ref(v_a_1333_);
lean_dec_ref_known(v_a_1332_, 1);
lean_dec_ref_known(v_a_1331_, 1);
lean_dec_ref_known(v_a_1330_, 1);
lean_dec_ref_known(v_a_1329_, 1);
v___x_1347_ = lean_box(0);
return v___x_1347_;
}
} else {
lean_dec_ref_known(v_a_1332_, 1);
lean_dec_ref_known(v_a_1331_, 1);
lean_dec_ref_known(v_a_1330_, 1);
lean_dec_ref_known(v_a_1329_, 1);
lean_dec_ref(v_arg_1147_);
v___x_1348_ = lean_box(0);
return v___x_1348_;
}
} else {
lean_dec_ref(v_a_1332_);
lean_dec_ref_known(v_a_1331_, 1);
lean_dec_ref_known(v_a_1330_, 1);
lean_dec_ref_known(v_a_1329_, 1);
lean_dec_ref(v_arg_1147_);
v___x_1349_ = lean_box(0);
return v___x_1349_;
}
} else {
lean_dec_ref_known(v_a_1331_, 1);
lean_dec_ref_known(v_a_1330_, 1);
lean_dec_ref_known(v_a_1329_, 1);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1350_ = lean_box(0);
return v___x_1350_;
}
} else {
lean_dec_ref(v_a_1331_);
lean_dec_ref_known(v_a_1330_, 1);
lean_dec_ref_known(v_a_1329_, 1);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1351_ = lean_box(0);
return v___x_1351_;
}
} else {
lean_dec_ref_known(v_a_1330_, 1);
lean_dec_ref_known(v_a_1329_, 1);
lean_dec_ref(v_arg_1314_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1352_ = lean_box(0);
return v___x_1352_;
}
} else {
lean_dec_ref(v_a_1330_);
lean_dec_ref_known(v_a_1329_, 1);
lean_dec_ref(v_arg_1314_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1353_ = lean_box(0);
return v___x_1353_;
}
} else {
lean_dec_ref_known(v_a_1329_, 1);
lean_dec_ref(v_arg_1315_);
lean_dec_ref(v_arg_1314_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1354_ = lean_box(0);
return v___x_1354_;
}
} else {
lean_dec_ref(v_a_1329_);
lean_dec_ref(v_arg_1315_);
lean_dec_ref(v_arg_1314_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1355_ = lean_box(0);
return v___x_1355_;
}
} else {
lean_dec_ref(v_arg_1316_);
lean_dec_ref(v_arg_1315_);
lean_dec_ref(v_arg_1314_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1356_ = lean_box(0);
return v___x_1356_;
}
}
                                                                                    }
                                                                                }
                                                                            } else {
                                                                                lean_dec_ref_known(
                                                                                    v_pre_1312_,
                                                                                    2,
                                                                                );
                                                                                lean_dec_ref_known(
                                                                                    v_pre_1311_,
                                                                                    2,
                                                                                );
                                                                                lean_dec_ref_known(v_declName_1310_, 2);
                                                                                lean_dec_ref_known(
                                                                                    v_fn_1262_, 2,
                                                                                );
                                                                                lean_dec_ref_known(
                                                                                    v_fn_1220_, 2,
                                                                                );
                                                                                lean_dec_ref_known(
                                                                                    v_fn_1148_, 2,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_1149_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_1147_,
                                                                                );
                                                                                v___x_1357_ =
                                                                                    lean_box(0);
                                                                                return v___x_1357_;
                                                                            }
                                                                        } else {
                                                                            lean_dec(v_pre_1312_);
                                                                            lean_dec_ref_known(
                                                                                v_pre_1311_,
                                                                                2,
                                                                            );
                                                                            lean_dec_ref_known(
                                                                                v_declName_1310_,
                                                                                2,
                                                                            );
                                                                            lean_dec_ref_known(
                                                                                v_fn_1262_, 2,
                                                                            );
                                                                            lean_dec_ref_known(
                                                                                v_fn_1220_, 2,
                                                                            );
                                                                            lean_dec_ref_known(
                                                                                v_fn_1148_, 2,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_1149_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_1147_,
                                                                            );
                                                                            v___x_1358_ =
                                                                                lean_box(0);
                                                                            return v___x_1358_;
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref_known(
                                                                            v_declName_1310_,
                                                                            2,
                                                                        );
                                                                        lean_dec(v_pre_1311_);
                                                                        lean_dec_ref_known(
                                                                            v_fn_1262_, 2,
                                                                        );
                                                                        lean_dec_ref_known(
                                                                            v_fn_1220_, 2,
                                                                        );
                                                                        lean_dec_ref_known(
                                                                            v_fn_1148_, 2,
                                                                        );
                                                                        lean_dec_ref(v_arg_1149_);
                                                                        lean_dec_ref(v_arg_1147_);
                                                                        v___x_1359_ = lean_box(0);
                                                                        return v___x_1359_;
                                                                    }
                                                                } else {
                                                                    lean_dec(v_declName_1310_);
                                                                    lean_dec_ref_known(
                                                                        v_fn_1262_, 2,
                                                                    );
                                                                    lean_dec_ref_known(
                                                                        v_fn_1220_, 2,
                                                                    );
                                                                    lean_dec_ref_known(
                                                                        v_fn_1148_, 2,
                                                                    );
                                                                    lean_dec_ref(v_arg_1149_);
                                                                    lean_dec_ref(v_arg_1147_);
                                                                    v___x_1360_ = lean_box(0);
                                                                    return v___x_1360_;
                                                                }
                                                            }
                                                            5 => {
                                                                lean_inc_ref(v_fn_1309_);
                                                                v_fn_1361_ =
                                                                    lean_ctor_get(v_fn_1309_, 0);
                                                                match lean_obj_tag(v_fn_1361_) {
                                                                    4 => {
                                                                        v_declName_1362_ =
                                                                            lean_ctor_get(
                                                                                v_fn_1361_, 0,
                                                                            );
                                                                        lean_inc(v_declName_1362_);
                                                                        if lean_obj_tag(
                                                                            v_declName_1362_,
                                                                        ) == 1
                                                                        {
                                                                            v_pre_1363_ = lean_ctor_get(v_declName_1362_, 0);
                                                                            lean_inc(v_pre_1363_);
                                                                            if lean_obj_tag(
                                                                                v_pre_1363_,
                                                                            ) == 1
                                                                            {
                                                                                v_pre_1364_ =
                                                                                    lean_ctor_get(
                                                                                        v_pre_1363_,
                                                                                        0,
                                                                                    );
                                                                                lean_inc(
                                                                                    v_pre_1364_,
                                                                                );
                                                                                if lean_obj_tag(
                                                                                    v_pre_1364_,
                                                                                ) == 1
                                                                                {
                                                                                    v_pre_1365_ = lean_ctor_get(v_pre_1364_, 0);
                                                                                    if lean_obj_tag(
                                                                                        v_pre_1365_,
                                                                                    ) == 0
                                                                                    {
                                                                                        v_arg_1366_ = lean_ctor_get(v_fn_1148_, 1);
                                                                                        lean_inc_ref(v_arg_1366_);
                                                                                        lean_dec_ref_known(v_fn_1148_, 2);
                                                                                        v_arg_1367_ = lean_ctor_get(v_fn_1220_, 1);
                                                                                        lean_inc_ref(v_arg_1367_);
                                                                                        lean_dec_ref_known(v_fn_1220_, 2);
                                                                                        v_arg_1368_ = lean_ctor_get(v_fn_1262_, 1);
                                                                                        lean_inc_ref(v_arg_1368_);
                                                                                        lean_dec_ref_known(v_fn_1262_, 2);
                                                                                        v_arg_1369_ = lean_ctor_get(v_fn_1309_, 1);
                                                                                        lean_inc_ref(v_arg_1369_);
                                                                                        lean_dec_ref_known(v_fn_1309_, 2);
                                                                                        v_str_1370_ = lean_ctor_get(v_declName_1362_, 1);
                                                                                        lean_inc_ref(v_str_1370_);
                                                                                        lean_dec_ref_known(v_declName_1362_, 2);
                                                                                        v_str_1371_ = lean_ctor_get(v_pre_1363_, 1);
                                                                                        lean_inc_ref(v_str_1371_);
                                                                                        lean_dec_ref_known(v_pre_1363_, 2);
                                                                                        v_str_1372_ = lean_ctor_get(v_pre_1364_, 1);
                                                                                        lean_inc_ref(v_str_1372_);
                                                                                        lean_dec_ref_known(v_pre_1364_, 2);
                                                                                        v___x_1373_ = l_Lean_Expr_name_x3f___closed__0;
                                                                                        v___x_1374_ = lean_string_dec_eq(v_str_1372_, v___x_1373_);
                                                                                        lean_dec_ref(v_str_1372_);
                                                                                        if v___x_1374_ == 0 {
lean_dec_ref(v_str_1371_);
lean_dec_ref(v_str_1370_);
lean_dec_ref(v_arg_1369_);
lean_dec_ref(v_arg_1368_);
lean_dec_ref(v_arg_1367_);
lean_dec_ref(v_arg_1366_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1375_ = lean_box(0);
return v___x_1375_;
} else {
v___x_1376_ = l_Lean_Expr_name_x3f___closed__1;
v___x_1377_ = lean_string_dec_eq(v_str_1371_, v___x_1376_);
lean_dec_ref(v_str_1371_);
if v___x_1377_ == 0 {
lean_dec_ref(v_str_1370_);
lean_dec_ref(v_arg_1369_);
lean_dec_ref(v_arg_1368_);
lean_dec_ref(v_arg_1367_);
lean_dec_ref(v_arg_1366_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1378_ = lean_box(0);
return v___x_1378_;
} else {
v___x_1379_ = l_Lean_Expr_name_x3f___closed__9;
v___x_1380_ = lean_string_dec_eq(v_str_1370_, v___x_1379_);
lean_dec_ref(v_str_1370_);
if v___x_1380_ == 0 {
lean_dec_ref(v_arg_1369_);
lean_dec_ref(v_arg_1368_);
lean_dec_ref(v_arg_1367_);
lean_dec_ref(v_arg_1366_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1381_ = lean_box(0);
return v___x_1381_;
} else {
if lean_obj_tag(v_arg_1369_) == 9 {
v_a_1382_ = lean_ctor_get(v_arg_1369_, 0);
lean_inc_ref(v_a_1382_);
lean_dec_ref_known(v_arg_1369_, 1);
if lean_obj_tag(v_a_1382_) == 1 {
if lean_obj_tag(v_arg_1368_) == 9 {
v_a_1383_ = lean_ctor_get(v_arg_1368_, 0);
lean_inc_ref(v_a_1383_);
lean_dec_ref_known(v_arg_1368_, 1);
if lean_obj_tag(v_a_1383_) == 1 {
if lean_obj_tag(v_arg_1367_) == 9 {
v_a_1384_ = lean_ctor_get(v_arg_1367_, 0);
lean_inc_ref(v_a_1384_);
lean_dec_ref_known(v_arg_1367_, 1);
if lean_obj_tag(v_a_1384_) == 1 {
if lean_obj_tag(v_arg_1366_) == 9 {
v_a_1385_ = lean_ctor_get(v_arg_1366_, 0);
lean_inc_ref(v_a_1385_);
lean_dec_ref_known(v_arg_1366_, 1);
if lean_obj_tag(v_a_1385_) == 1 {
if lean_obj_tag(v_arg_1149_) == 9 {
v_a_1386_ = lean_ctor_get(v_arg_1149_, 0);
lean_inc_ref(v_a_1386_);
lean_dec_ref_known(v_arg_1149_, 1);
if lean_obj_tag(v_a_1386_) == 1 {
if lean_obj_tag(v_arg_1147_) == 9 {
v_a_1387_ = lean_ctor_get(v_arg_1147_, 0);
lean_inc_ref(v_a_1387_);
lean_dec_ref_known(v_arg_1147_, 1);
if lean_obj_tag(v_a_1387_) == 1 {
v_val_1388_ = lean_ctor_get(v_a_1382_, 0);
lean_inc_ref(v_val_1388_);
lean_dec_ref_known(v_a_1382_, 1);
v_val_1389_ = lean_ctor_get(v_a_1383_, 0);
lean_inc_ref(v_val_1389_);
lean_dec_ref_known(v_a_1383_, 1);
v_val_1390_ = lean_ctor_get(v_a_1384_, 0);
lean_inc_ref(v_val_1390_);
lean_dec_ref_known(v_a_1384_, 1);
v_val_1391_ = lean_ctor_get(v_a_1385_, 0);
lean_inc_ref(v_val_1391_);
lean_dec_ref_known(v_a_1385_, 1);
v_val_1392_ = lean_ctor_get(v_a_1386_, 0);
lean_inc_ref(v_val_1392_);
lean_dec_ref_known(v_a_1386_, 1);
v_val_1393_ = lean_ctor_get(v_a_1387_, 0);
v_isSharedCheck_1401_ = (!lean_is_exclusive(v_a_1387_)) as u8;
if v_isSharedCheck_1401_ == 0 {
v___x_1395_ = v_a_1387_;
v_isShared_1396_ = v_isSharedCheck_1401_;
state = 14; continue;
} else {
lean_inc(v_val_1393_);
lean_dec(v_a_1387_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1401_;
state = 14; continue;
}
} else {
lean_dec_ref(v_a_1387_);
lean_dec_ref_known(v_a_1386_, 1);
lean_dec_ref_known(v_a_1385_, 1);
lean_dec_ref_known(v_a_1384_, 1);
lean_dec_ref_known(v_a_1383_, 1);
lean_dec_ref_known(v_a_1382_, 1);
v___x_1402_ = lean_box(0);
return v___x_1402_;
}
} else {
lean_dec_ref_known(v_a_1386_, 1);
lean_dec_ref_known(v_a_1385_, 1);
lean_dec_ref_known(v_a_1384_, 1);
lean_dec_ref_known(v_a_1383_, 1);
lean_dec_ref_known(v_a_1382_, 1);
lean_dec_ref(v_arg_1147_);
v___x_1403_ = lean_box(0);
return v___x_1403_;
}
} else {
lean_dec_ref(v_a_1386_);
lean_dec_ref_known(v_a_1385_, 1);
lean_dec_ref_known(v_a_1384_, 1);
lean_dec_ref_known(v_a_1383_, 1);
lean_dec_ref_known(v_a_1382_, 1);
lean_dec_ref(v_arg_1147_);
v___x_1404_ = lean_box(0);
return v___x_1404_;
}
} else {
lean_dec_ref_known(v_a_1385_, 1);
lean_dec_ref_known(v_a_1384_, 1);
lean_dec_ref_known(v_a_1383_, 1);
lean_dec_ref_known(v_a_1382_, 1);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1405_ = lean_box(0);
return v___x_1405_;
}
} else {
lean_dec_ref(v_a_1385_);
lean_dec_ref_known(v_a_1384_, 1);
lean_dec_ref_known(v_a_1383_, 1);
lean_dec_ref_known(v_a_1382_, 1);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1406_ = lean_box(0);
return v___x_1406_;
}
} else {
lean_dec_ref_known(v_a_1384_, 1);
lean_dec_ref_known(v_a_1383_, 1);
lean_dec_ref_known(v_a_1382_, 1);
lean_dec_ref(v_arg_1366_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1407_ = lean_box(0);
return v___x_1407_;
}
} else {
lean_dec_ref(v_a_1384_);
lean_dec_ref_known(v_a_1383_, 1);
lean_dec_ref_known(v_a_1382_, 1);
lean_dec_ref(v_arg_1366_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1408_ = lean_box(0);
return v___x_1408_;
}
} else {
lean_dec_ref_known(v_a_1383_, 1);
lean_dec_ref_known(v_a_1382_, 1);
lean_dec_ref(v_arg_1367_);
lean_dec_ref(v_arg_1366_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1409_ = lean_box(0);
return v___x_1409_;
}
} else {
lean_dec_ref(v_a_1383_);
lean_dec_ref_known(v_a_1382_, 1);
lean_dec_ref(v_arg_1367_);
lean_dec_ref(v_arg_1366_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1410_ = lean_box(0);
return v___x_1410_;
}
} else {
lean_dec_ref_known(v_a_1382_, 1);
lean_dec_ref(v_arg_1368_);
lean_dec_ref(v_arg_1367_);
lean_dec_ref(v_arg_1366_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1411_ = lean_box(0);
return v___x_1411_;
}
} else {
lean_dec_ref(v_a_1382_);
lean_dec_ref(v_arg_1368_);
lean_dec_ref(v_arg_1367_);
lean_dec_ref(v_arg_1366_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1412_ = lean_box(0);
return v___x_1412_;
}
} else {
lean_dec_ref(v_arg_1369_);
lean_dec_ref(v_arg_1368_);
lean_dec_ref(v_arg_1367_);
lean_dec_ref(v_arg_1366_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1413_ = lean_box(0);
return v___x_1413_;
}
}
}
}
                                                                                    } else {
                                                                                        lean_dec_ref_known(v_pre_1364_, 2);
                                                                                        lean_dec_ref_known(v_pre_1363_, 2);
                                                                                        lean_dec_ref_known(v_declName_1362_, 2);
                                                                                        lean_dec_ref_known(v_fn_1309_, 2);
                                                                                        lean_dec_ref_known(v_fn_1262_, 2);
                                                                                        lean_dec_ref_known(v_fn_1220_, 2);
                                                                                        lean_dec_ref_known(v_fn_1148_, 2);
                                                                                        lean_dec_ref(v_arg_1149_);
                                                                                        lean_dec_ref(v_arg_1147_);
                                                                                        v___x_1414_ = lean_box(0);
                                                                                        return v___x_1414_;
                                                                                    }
                                                                                } else {
                                                                                    lean_dec_ref_known(v_pre_1363_, 2);
                                                                                    lean_dec(
                                                                                        v_pre_1364_,
                                                                                    );
                                                                                    lean_dec_ref_known(v_declName_1362_, 2);
                                                                                    lean_dec_ref_known(v_fn_1309_, 2);
                                                                                    lean_dec_ref_known(v_fn_1262_, 2);
                                                                                    lean_dec_ref_known(v_fn_1220_, 2);
                                                                                    lean_dec_ref_known(v_fn_1148_, 2);
                                                                                    lean_dec_ref(
                                                                                        v_arg_1149_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_arg_1147_,
                                                                                    );
                                                                                    v___x_1415_ =
                                                                                        lean_box(0);
                                                                                    return v___x_1415_;
                                                                                }
                                                                            } else {
                                                                                lean_dec_ref_known(v_declName_1362_, 2);
                                                                                lean_dec(
                                                                                    v_pre_1363_,
                                                                                );
                                                                                lean_dec_ref_known(
                                                                                    v_fn_1309_, 2,
                                                                                );
                                                                                lean_dec_ref_known(
                                                                                    v_fn_1262_, 2,
                                                                                );
                                                                                lean_dec_ref_known(
                                                                                    v_fn_1220_, 2,
                                                                                );
                                                                                lean_dec_ref_known(
                                                                                    v_fn_1148_, 2,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_1149_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_1147_,
                                                                                );
                                                                                v___x_1416_ =
                                                                                    lean_box(0);
                                                                                return v___x_1416_;
                                                                            }
                                                                        } else {
                                                                            lean_dec(
                                                                                v_declName_1362_,
                                                                            );
                                                                            lean_dec_ref_known(
                                                                                v_fn_1309_, 2,
                                                                            );
                                                                            lean_dec_ref_known(
                                                                                v_fn_1262_, 2,
                                                                            );
                                                                            lean_dec_ref_known(
                                                                                v_fn_1220_, 2,
                                                                            );
                                                                            lean_dec_ref_known(
                                                                                v_fn_1148_, 2,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_1149_,
                                                                            );
                                                                            lean_dec_ref(
                                                                                v_arg_1147_,
                                                                            );
                                                                            v___x_1417_ =
                                                                                lean_box(0);
                                                                            return v___x_1417_;
                                                                        }
                                                                    }
                                                                    5 => {
                                                                        lean_inc_ref(v_fn_1361_);
                                                                        v_fn_1418_ = lean_ctor_get(
                                                                            v_fn_1361_, 0,
                                                                        );
                                                                        match lean_obj_tag(
                                                                            v_fn_1418_,
                                                                        ) {
                                                                            4 => {
                                                                                v_declName_1419_ =
                                                                                    lean_ctor_get(
                                                                                        v_fn_1418_,
                                                                                        0,
                                                                                    );
                                                                                lean_inc(v_declName_1419_);
                                                                                if lean_obj_tag(v_declName_1419_) == 1 {
v_pre_1420_ = lean_ctor_get(v_declName_1419_, 0);
lean_inc(v_pre_1420_);
if lean_obj_tag(v_pre_1420_) == 1 {
v_pre_1421_ = lean_ctor_get(v_pre_1420_, 0);
lean_inc(v_pre_1421_);
if lean_obj_tag(v_pre_1421_) == 1 {
v_pre_1422_ = lean_ctor_get(v_pre_1421_, 0);
if lean_obj_tag(v_pre_1422_) == 0 {
v_arg_1423_ = lean_ctor_get(v_fn_1148_, 1);
lean_inc_ref(v_arg_1423_);
lean_dec_ref_known(v_fn_1148_, 2);
v_arg_1424_ = lean_ctor_get(v_fn_1220_, 1);
lean_inc_ref(v_arg_1424_);
lean_dec_ref_known(v_fn_1220_, 2);
v_arg_1425_ = lean_ctor_get(v_fn_1262_, 1);
lean_inc_ref(v_arg_1425_);
lean_dec_ref_known(v_fn_1262_, 2);
v_arg_1426_ = lean_ctor_get(v_fn_1309_, 1);
lean_inc_ref(v_arg_1426_);
lean_dec_ref_known(v_fn_1309_, 2);
v_arg_1427_ = lean_ctor_get(v_fn_1361_, 1);
lean_inc_ref(v_arg_1427_);
lean_dec_ref_known(v_fn_1361_, 2);
v_str_1428_ = lean_ctor_get(v_declName_1419_, 1);
lean_inc_ref(v_str_1428_);
lean_dec_ref_known(v_declName_1419_, 2);
v_str_1429_ = lean_ctor_get(v_pre_1420_, 1);
lean_inc_ref(v_str_1429_);
lean_dec_ref_known(v_pre_1420_, 2);
v_str_1430_ = lean_ctor_get(v_pre_1421_, 1);
lean_inc_ref(v_str_1430_);
lean_dec_ref_known(v_pre_1421_, 2);
v___x_1431_ = l_Lean_Expr_name_x3f___closed__0;
v___x_1432_ = lean_string_dec_eq(v_str_1430_, v___x_1431_);
lean_dec_ref(v_str_1430_);
if v___x_1432_ == 0 {
lean_dec_ref(v_str_1429_);
lean_dec_ref(v_str_1428_);
lean_dec_ref(v_arg_1427_);
lean_dec_ref(v_arg_1426_);
lean_dec_ref(v_arg_1425_);
lean_dec_ref(v_arg_1424_);
lean_dec_ref(v_arg_1423_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1433_ = lean_box(0);
return v___x_1433_;
} else {
v___x_1434_ = l_Lean_Expr_name_x3f___closed__1;
v___x_1435_ = lean_string_dec_eq(v_str_1429_, v___x_1434_);
lean_dec_ref(v_str_1429_);
if v___x_1435_ == 0 {
lean_dec_ref(v_str_1428_);
lean_dec_ref(v_arg_1427_);
lean_dec_ref(v_arg_1426_);
lean_dec_ref(v_arg_1425_);
lean_dec_ref(v_arg_1424_);
lean_dec_ref(v_arg_1423_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1436_ = lean_box(0);
return v___x_1436_;
} else {
v___x_1437_ = l_Lean_Expr_name_x3f___closed__10;
v___x_1438_ = lean_string_dec_eq(v_str_1428_, v___x_1437_);
lean_dec_ref(v_str_1428_);
if v___x_1438_ == 0 {
lean_dec_ref(v_arg_1427_);
lean_dec_ref(v_arg_1426_);
lean_dec_ref(v_arg_1425_);
lean_dec_ref(v_arg_1424_);
lean_dec_ref(v_arg_1423_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1439_ = lean_box(0);
return v___x_1439_;
} else {
if lean_obj_tag(v_arg_1427_) == 9 {
v_a_1440_ = lean_ctor_get(v_arg_1427_, 0);
lean_inc_ref(v_a_1440_);
lean_dec_ref_known(v_arg_1427_, 1);
if lean_obj_tag(v_a_1440_) == 1 {
if lean_obj_tag(v_arg_1426_) == 9 {
v_a_1441_ = lean_ctor_get(v_arg_1426_, 0);
lean_inc_ref(v_a_1441_);
lean_dec_ref_known(v_arg_1426_, 1);
if lean_obj_tag(v_a_1441_) == 1 {
if lean_obj_tag(v_arg_1425_) == 9 {
v_a_1442_ = lean_ctor_get(v_arg_1425_, 0);
lean_inc_ref(v_a_1442_);
lean_dec_ref_known(v_arg_1425_, 1);
if lean_obj_tag(v_a_1442_) == 1 {
if lean_obj_tag(v_arg_1424_) == 9 {
v_a_1443_ = lean_ctor_get(v_arg_1424_, 0);
lean_inc_ref(v_a_1443_);
lean_dec_ref_known(v_arg_1424_, 1);
if lean_obj_tag(v_a_1443_) == 1 {
if lean_obj_tag(v_arg_1423_) == 9 {
v_a_1444_ = lean_ctor_get(v_arg_1423_, 0);
lean_inc_ref(v_a_1444_);
lean_dec_ref_known(v_arg_1423_, 1);
if lean_obj_tag(v_a_1444_) == 1 {
if lean_obj_tag(v_arg_1149_) == 9 {
v_a_1445_ = lean_ctor_get(v_arg_1149_, 0);
lean_inc_ref(v_a_1445_);
lean_dec_ref_known(v_arg_1149_, 1);
if lean_obj_tag(v_a_1445_) == 1 {
if lean_obj_tag(v_arg_1147_) == 9 {
v_a_1446_ = lean_ctor_get(v_arg_1147_, 0);
lean_inc_ref(v_a_1446_);
lean_dec_ref_known(v_arg_1147_, 1);
if lean_obj_tag(v_a_1446_) == 1 {
v_val_1447_ = lean_ctor_get(v_a_1440_, 0);
lean_inc_ref(v_val_1447_);
lean_dec_ref_known(v_a_1440_, 1);
v_val_1448_ = lean_ctor_get(v_a_1441_, 0);
lean_inc_ref(v_val_1448_);
lean_dec_ref_known(v_a_1441_, 1);
v_val_1449_ = lean_ctor_get(v_a_1442_, 0);
lean_inc_ref(v_val_1449_);
lean_dec_ref_known(v_a_1442_, 1);
v_val_1450_ = lean_ctor_get(v_a_1443_, 0);
lean_inc_ref(v_val_1450_);
lean_dec_ref_known(v_a_1443_, 1);
v_val_1451_ = lean_ctor_get(v_a_1444_, 0);
lean_inc_ref(v_val_1451_);
lean_dec_ref_known(v_a_1444_, 1);
v_val_1452_ = lean_ctor_get(v_a_1445_, 0);
lean_inc_ref(v_val_1452_);
lean_dec_ref_known(v_a_1445_, 1);
v_val_1453_ = lean_ctor_get(v_a_1446_, 0);
v_isSharedCheck_1461_ = (!lean_is_exclusive(v_a_1446_)) as u8;
if v_isSharedCheck_1461_ == 0 {
v___x_1455_ = v_a_1446_;
v_isShared_1456_ = v_isSharedCheck_1461_;
state = 16; continue;
} else {
lean_inc(v_val_1453_);
lean_dec(v_a_1446_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1461_;
state = 16; continue;
}
} else {
lean_dec_ref(v_a_1446_);
lean_dec_ref_known(v_a_1445_, 1);
lean_dec_ref_known(v_a_1444_, 1);
lean_dec_ref_known(v_a_1443_, 1);
lean_dec_ref_known(v_a_1442_, 1);
lean_dec_ref_known(v_a_1441_, 1);
lean_dec_ref_known(v_a_1440_, 1);
v___x_1462_ = lean_box(0);
return v___x_1462_;
}
} else {
lean_dec_ref_known(v_a_1445_, 1);
lean_dec_ref_known(v_a_1444_, 1);
lean_dec_ref_known(v_a_1443_, 1);
lean_dec_ref_known(v_a_1442_, 1);
lean_dec_ref_known(v_a_1441_, 1);
lean_dec_ref_known(v_a_1440_, 1);
lean_dec_ref(v_arg_1147_);
v___x_1463_ = lean_box(0);
return v___x_1463_;
}
} else {
lean_dec_ref(v_a_1445_);
lean_dec_ref_known(v_a_1444_, 1);
lean_dec_ref_known(v_a_1443_, 1);
lean_dec_ref_known(v_a_1442_, 1);
lean_dec_ref_known(v_a_1441_, 1);
lean_dec_ref_known(v_a_1440_, 1);
lean_dec_ref(v_arg_1147_);
v___x_1464_ = lean_box(0);
return v___x_1464_;
}
} else {
lean_dec_ref_known(v_a_1444_, 1);
lean_dec_ref_known(v_a_1443_, 1);
lean_dec_ref_known(v_a_1442_, 1);
lean_dec_ref_known(v_a_1441_, 1);
lean_dec_ref_known(v_a_1440_, 1);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1465_ = lean_box(0);
return v___x_1465_;
}
} else {
lean_dec_ref(v_a_1444_);
lean_dec_ref_known(v_a_1443_, 1);
lean_dec_ref_known(v_a_1442_, 1);
lean_dec_ref_known(v_a_1441_, 1);
lean_dec_ref_known(v_a_1440_, 1);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1466_ = lean_box(0);
return v___x_1466_;
}
} else {
lean_dec_ref_known(v_a_1443_, 1);
lean_dec_ref_known(v_a_1442_, 1);
lean_dec_ref_known(v_a_1441_, 1);
lean_dec_ref_known(v_a_1440_, 1);
lean_dec_ref(v_arg_1423_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1467_ = lean_box(0);
return v___x_1467_;
}
} else {
lean_dec_ref(v_a_1443_);
lean_dec_ref_known(v_a_1442_, 1);
lean_dec_ref_known(v_a_1441_, 1);
lean_dec_ref_known(v_a_1440_, 1);
lean_dec_ref(v_arg_1423_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1468_ = lean_box(0);
return v___x_1468_;
}
} else {
lean_dec_ref_known(v_a_1442_, 1);
lean_dec_ref_known(v_a_1441_, 1);
lean_dec_ref_known(v_a_1440_, 1);
lean_dec_ref(v_arg_1424_);
lean_dec_ref(v_arg_1423_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1469_ = lean_box(0);
return v___x_1469_;
}
} else {
lean_dec_ref(v_a_1442_);
lean_dec_ref_known(v_a_1441_, 1);
lean_dec_ref_known(v_a_1440_, 1);
lean_dec_ref(v_arg_1424_);
lean_dec_ref(v_arg_1423_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1470_ = lean_box(0);
return v___x_1470_;
}
} else {
lean_dec_ref_known(v_a_1441_, 1);
lean_dec_ref_known(v_a_1440_, 1);
lean_dec_ref(v_arg_1425_);
lean_dec_ref(v_arg_1424_);
lean_dec_ref(v_arg_1423_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1471_ = lean_box(0);
return v___x_1471_;
}
} else {
lean_dec_ref(v_a_1441_);
lean_dec_ref_known(v_a_1440_, 1);
lean_dec_ref(v_arg_1425_);
lean_dec_ref(v_arg_1424_);
lean_dec_ref(v_arg_1423_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1472_ = lean_box(0);
return v___x_1472_;
}
} else {
lean_dec_ref_known(v_a_1440_, 1);
lean_dec_ref(v_arg_1426_);
lean_dec_ref(v_arg_1425_);
lean_dec_ref(v_arg_1424_);
lean_dec_ref(v_arg_1423_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1473_ = lean_box(0);
return v___x_1473_;
}
} else {
lean_dec_ref(v_a_1440_);
lean_dec_ref(v_arg_1426_);
lean_dec_ref(v_arg_1425_);
lean_dec_ref(v_arg_1424_);
lean_dec_ref(v_arg_1423_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1474_ = lean_box(0);
return v___x_1474_;
}
} else {
lean_dec_ref(v_arg_1427_);
lean_dec_ref(v_arg_1426_);
lean_dec_ref(v_arg_1425_);
lean_dec_ref(v_arg_1424_);
lean_dec_ref(v_arg_1423_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1475_ = lean_box(0);
return v___x_1475_;
}
}
}
}
} else {
lean_dec_ref_known(v_pre_1421_, 2);
lean_dec_ref_known(v_pre_1420_, 2);
lean_dec_ref_known(v_declName_1419_, 2);
lean_dec_ref_known(v_fn_1361_, 2);
lean_dec_ref_known(v_fn_1309_, 2);
lean_dec_ref_known(v_fn_1262_, 2);
lean_dec_ref_known(v_fn_1220_, 2);
lean_dec_ref_known(v_fn_1148_, 2);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1476_ = lean_box(0);
return v___x_1476_;
}
} else {
lean_dec_ref_known(v_pre_1420_, 2);
lean_dec(v_pre_1421_);
lean_dec_ref_known(v_declName_1419_, 2);
lean_dec_ref_known(v_fn_1361_, 2);
lean_dec_ref_known(v_fn_1309_, 2);
lean_dec_ref_known(v_fn_1262_, 2);
lean_dec_ref_known(v_fn_1220_, 2);
lean_dec_ref_known(v_fn_1148_, 2);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1477_ = lean_box(0);
return v___x_1477_;
}
} else {
lean_dec(v_pre_1420_);
lean_dec_ref_known(v_declName_1419_, 2);
lean_dec_ref_known(v_fn_1361_, 2);
lean_dec_ref_known(v_fn_1309_, 2);
lean_dec_ref_known(v_fn_1262_, 2);
lean_dec_ref_known(v_fn_1220_, 2);
lean_dec_ref_known(v_fn_1148_, 2);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1478_ = lean_box(0);
return v___x_1478_;
}
} else {
lean_dec(v_declName_1419_);
lean_dec_ref_known(v_fn_1361_, 2);
lean_dec_ref_known(v_fn_1309_, 2);
lean_dec_ref_known(v_fn_1262_, 2);
lean_dec_ref_known(v_fn_1220_, 2);
lean_dec_ref_known(v_fn_1148_, 2);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1479_ = lean_box(0);
return v___x_1479_;
}
                                                                            }
                                                                            5 => {
                                                                                lean_inc_ref(
                                                                                    v_fn_1418_,
                                                                                );
                                                                                v_fn_1480_ =
                                                                                    lean_ctor_get(
                                                                                        v_fn_1418_,
                                                                                        0,
                                                                                    );
                                                                                if lean_obj_tag(
                                                                                    v_fn_1480_,
                                                                                ) == 4
                                                                                {
                                                                                    v_declName_1481_ = lean_ctor_get(v_fn_1480_, 0);
                                                                                    lean_inc(v_declName_1481_);
                                                                                    if lean_obj_tag(v_declName_1481_) == 1 {
v_pre_1482_ = lean_ctor_get(v_declName_1481_, 0);
lean_inc(v_pre_1482_);
if lean_obj_tag(v_pre_1482_) == 1 {
v_pre_1483_ = lean_ctor_get(v_pre_1482_, 0);
lean_inc(v_pre_1483_);
if lean_obj_tag(v_pre_1483_) == 1 {
v_pre_1484_ = lean_ctor_get(v_pre_1483_, 0);
if lean_obj_tag(v_pre_1484_) == 0 {
v_arg_1485_ = lean_ctor_get(v_fn_1148_, 1);
lean_inc_ref(v_arg_1485_);
lean_dec_ref_known(v_fn_1148_, 2);
v_arg_1486_ = lean_ctor_get(v_fn_1220_, 1);
lean_inc_ref(v_arg_1486_);
lean_dec_ref_known(v_fn_1220_, 2);
v_arg_1487_ = lean_ctor_get(v_fn_1262_, 1);
lean_inc_ref(v_arg_1487_);
lean_dec_ref_known(v_fn_1262_, 2);
v_arg_1488_ = lean_ctor_get(v_fn_1309_, 1);
lean_inc_ref(v_arg_1488_);
lean_dec_ref_known(v_fn_1309_, 2);
v_arg_1489_ = lean_ctor_get(v_fn_1361_, 1);
lean_inc_ref(v_arg_1489_);
lean_dec_ref_known(v_fn_1361_, 2);
v_arg_1490_ = lean_ctor_get(v_fn_1418_, 1);
lean_inc_ref(v_arg_1490_);
lean_dec_ref_known(v_fn_1418_, 2);
v_str_1491_ = lean_ctor_get(v_declName_1481_, 1);
lean_inc_ref(v_str_1491_);
lean_dec_ref_known(v_declName_1481_, 2);
v_str_1492_ = lean_ctor_get(v_pre_1482_, 1);
lean_inc_ref(v_str_1492_);
lean_dec_ref_known(v_pre_1482_, 2);
v_str_1493_ = lean_ctor_get(v_pre_1483_, 1);
lean_inc_ref(v_str_1493_);
lean_dec_ref_known(v_pre_1483_, 2);
v___x_1494_ = l_Lean_Expr_name_x3f___closed__0;
v___x_1495_ = lean_string_dec_eq(v_str_1493_, v___x_1494_);
lean_dec_ref(v_str_1493_);
if v___x_1495_ == 0 {
lean_dec_ref(v_str_1492_);
lean_dec_ref(v_str_1491_);
lean_dec_ref(v_arg_1490_);
lean_dec_ref(v_arg_1489_);
lean_dec_ref(v_arg_1488_);
lean_dec_ref(v_arg_1487_);
lean_dec_ref(v_arg_1486_);
lean_dec_ref(v_arg_1485_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1496_ = lean_box(0);
return v___x_1496_;
} else {
v___x_1497_ = l_Lean_Expr_name_x3f___closed__1;
v___x_1498_ = lean_string_dec_eq(v_str_1492_, v___x_1497_);
lean_dec_ref(v_str_1492_);
if v___x_1498_ == 0 {
lean_dec_ref(v_str_1491_);
lean_dec_ref(v_arg_1490_);
lean_dec_ref(v_arg_1489_);
lean_dec_ref(v_arg_1488_);
lean_dec_ref(v_arg_1487_);
lean_dec_ref(v_arg_1486_);
lean_dec_ref(v_arg_1485_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1499_ = lean_box(0);
return v___x_1499_;
} else {
v___x_1500_ = l_Lean_Expr_name_x3f___closed__11;
v___x_1501_ = lean_string_dec_eq(v_str_1491_, v___x_1500_);
lean_dec_ref(v_str_1491_);
if v___x_1501_ == 0 {
lean_dec_ref(v_arg_1490_);
lean_dec_ref(v_arg_1489_);
lean_dec_ref(v_arg_1488_);
lean_dec_ref(v_arg_1487_);
lean_dec_ref(v_arg_1486_);
lean_dec_ref(v_arg_1485_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1502_ = lean_box(0);
return v___x_1502_;
} else {
if lean_obj_tag(v_arg_1490_) == 9 {
v_a_1503_ = lean_ctor_get(v_arg_1490_, 0);
lean_inc_ref(v_a_1503_);
lean_dec_ref_known(v_arg_1490_, 1);
if lean_obj_tag(v_a_1503_) == 1 {
if lean_obj_tag(v_arg_1489_) == 9 {
v_a_1504_ = lean_ctor_get(v_arg_1489_, 0);
lean_inc_ref(v_a_1504_);
lean_dec_ref_known(v_arg_1489_, 1);
if lean_obj_tag(v_a_1504_) == 1 {
if lean_obj_tag(v_arg_1488_) == 9 {
v_a_1505_ = lean_ctor_get(v_arg_1488_, 0);
lean_inc_ref(v_a_1505_);
lean_dec_ref_known(v_arg_1488_, 1);
if lean_obj_tag(v_a_1505_) == 1 {
if lean_obj_tag(v_arg_1487_) == 9 {
v_a_1506_ = lean_ctor_get(v_arg_1487_, 0);
lean_inc_ref(v_a_1506_);
lean_dec_ref_known(v_arg_1487_, 1);
if lean_obj_tag(v_a_1506_) == 1 {
if lean_obj_tag(v_arg_1486_) == 9 {
v_a_1507_ = lean_ctor_get(v_arg_1486_, 0);
lean_inc_ref(v_a_1507_);
lean_dec_ref_known(v_arg_1486_, 1);
if lean_obj_tag(v_a_1507_) == 1 {
if lean_obj_tag(v_arg_1485_) == 9 {
v_a_1508_ = lean_ctor_get(v_arg_1485_, 0);
lean_inc_ref(v_a_1508_);
lean_dec_ref_known(v_arg_1485_, 1);
if lean_obj_tag(v_a_1508_) == 1 {
if lean_obj_tag(v_arg_1149_) == 9 {
v_a_1509_ = lean_ctor_get(v_arg_1149_, 0);
lean_inc_ref(v_a_1509_);
lean_dec_ref_known(v_arg_1149_, 1);
if lean_obj_tag(v_a_1509_) == 1 {
if lean_obj_tag(v_arg_1147_) == 9 {
v_a_1510_ = lean_ctor_get(v_arg_1147_, 0);
lean_inc_ref(v_a_1510_);
lean_dec_ref_known(v_arg_1147_, 1);
if lean_obj_tag(v_a_1510_) == 1 {
v_val_1511_ = lean_ctor_get(v_a_1503_, 0);
lean_inc_ref(v_val_1511_);
lean_dec_ref_known(v_a_1503_, 1);
v_val_1512_ = lean_ctor_get(v_a_1504_, 0);
lean_inc_ref(v_val_1512_);
lean_dec_ref_known(v_a_1504_, 1);
v_val_1513_ = lean_ctor_get(v_a_1505_, 0);
lean_inc_ref(v_val_1513_);
lean_dec_ref_known(v_a_1505_, 1);
v_val_1514_ = lean_ctor_get(v_a_1506_, 0);
lean_inc_ref(v_val_1514_);
lean_dec_ref_known(v_a_1506_, 1);
v_val_1515_ = lean_ctor_get(v_a_1507_, 0);
lean_inc_ref(v_val_1515_);
lean_dec_ref_known(v_a_1507_, 1);
v_val_1516_ = lean_ctor_get(v_a_1508_, 0);
lean_inc_ref(v_val_1516_);
lean_dec_ref_known(v_a_1508_, 1);
v_val_1517_ = lean_ctor_get(v_a_1509_, 0);
lean_inc_ref(v_val_1517_);
lean_dec_ref_known(v_a_1509_, 1);
v_val_1518_ = lean_ctor_get(v_a_1510_, 0);
v_isSharedCheck_1526_ = (!lean_is_exclusive(v_a_1510_)) as u8;
if v_isSharedCheck_1526_ == 0 {
v___x_1520_ = v_a_1510_;
v_isShared_1521_ = v_isSharedCheck_1526_;
state = 18; continue;
} else {
lean_inc(v_val_1518_);
lean_dec(v_a_1510_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1526_;
state = 18; continue;
}
} else {
lean_dec_ref(v_a_1510_);
lean_dec_ref_known(v_a_1509_, 1);
lean_dec_ref_known(v_a_1508_, 1);
lean_dec_ref_known(v_a_1507_, 1);
lean_dec_ref_known(v_a_1506_, 1);
lean_dec_ref_known(v_a_1505_, 1);
lean_dec_ref_known(v_a_1504_, 1);
lean_dec_ref_known(v_a_1503_, 1);
v___x_1527_ = lean_box(0);
return v___x_1527_;
}
} else {
lean_dec_ref_known(v_a_1509_, 1);
lean_dec_ref_known(v_a_1508_, 1);
lean_dec_ref_known(v_a_1507_, 1);
lean_dec_ref_known(v_a_1506_, 1);
lean_dec_ref_known(v_a_1505_, 1);
lean_dec_ref_known(v_a_1504_, 1);
lean_dec_ref_known(v_a_1503_, 1);
lean_dec_ref(v_arg_1147_);
v___x_1528_ = lean_box(0);
return v___x_1528_;
}
} else {
lean_dec_ref(v_a_1509_);
lean_dec_ref_known(v_a_1508_, 1);
lean_dec_ref_known(v_a_1507_, 1);
lean_dec_ref_known(v_a_1506_, 1);
lean_dec_ref_known(v_a_1505_, 1);
lean_dec_ref_known(v_a_1504_, 1);
lean_dec_ref_known(v_a_1503_, 1);
lean_dec_ref(v_arg_1147_);
v___x_1529_ = lean_box(0);
return v___x_1529_;
}
} else {
lean_dec_ref_known(v_a_1508_, 1);
lean_dec_ref_known(v_a_1507_, 1);
lean_dec_ref_known(v_a_1506_, 1);
lean_dec_ref_known(v_a_1505_, 1);
lean_dec_ref_known(v_a_1504_, 1);
lean_dec_ref_known(v_a_1503_, 1);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1530_ = lean_box(0);
return v___x_1530_;
}
} else {
lean_dec_ref(v_a_1508_);
lean_dec_ref_known(v_a_1507_, 1);
lean_dec_ref_known(v_a_1506_, 1);
lean_dec_ref_known(v_a_1505_, 1);
lean_dec_ref_known(v_a_1504_, 1);
lean_dec_ref_known(v_a_1503_, 1);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1531_ = lean_box(0);
return v___x_1531_;
}
} else {
lean_dec_ref_known(v_a_1507_, 1);
lean_dec_ref_known(v_a_1506_, 1);
lean_dec_ref_known(v_a_1505_, 1);
lean_dec_ref_known(v_a_1504_, 1);
lean_dec_ref_known(v_a_1503_, 1);
lean_dec_ref(v_arg_1485_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1532_ = lean_box(0);
return v___x_1532_;
}
} else {
lean_dec_ref(v_a_1507_);
lean_dec_ref_known(v_a_1506_, 1);
lean_dec_ref_known(v_a_1505_, 1);
lean_dec_ref_known(v_a_1504_, 1);
lean_dec_ref_known(v_a_1503_, 1);
lean_dec_ref(v_arg_1485_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1533_ = lean_box(0);
return v___x_1533_;
}
} else {
lean_dec_ref_known(v_a_1506_, 1);
lean_dec_ref_known(v_a_1505_, 1);
lean_dec_ref_known(v_a_1504_, 1);
lean_dec_ref_known(v_a_1503_, 1);
lean_dec_ref(v_arg_1486_);
lean_dec_ref(v_arg_1485_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1534_ = lean_box(0);
return v___x_1534_;
}
} else {
lean_dec_ref(v_a_1506_);
lean_dec_ref_known(v_a_1505_, 1);
lean_dec_ref_known(v_a_1504_, 1);
lean_dec_ref_known(v_a_1503_, 1);
lean_dec_ref(v_arg_1486_);
lean_dec_ref(v_arg_1485_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1535_ = lean_box(0);
return v___x_1535_;
}
} else {
lean_dec_ref_known(v_a_1505_, 1);
lean_dec_ref_known(v_a_1504_, 1);
lean_dec_ref_known(v_a_1503_, 1);
lean_dec_ref(v_arg_1487_);
lean_dec_ref(v_arg_1486_);
lean_dec_ref(v_arg_1485_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1536_ = lean_box(0);
return v___x_1536_;
}
} else {
lean_dec_ref(v_a_1505_);
lean_dec_ref_known(v_a_1504_, 1);
lean_dec_ref_known(v_a_1503_, 1);
lean_dec_ref(v_arg_1487_);
lean_dec_ref(v_arg_1486_);
lean_dec_ref(v_arg_1485_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1537_ = lean_box(0);
return v___x_1537_;
}
} else {
lean_dec_ref_known(v_a_1504_, 1);
lean_dec_ref_known(v_a_1503_, 1);
lean_dec_ref(v_arg_1488_);
lean_dec_ref(v_arg_1487_);
lean_dec_ref(v_arg_1486_);
lean_dec_ref(v_arg_1485_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1538_ = lean_box(0);
return v___x_1538_;
}
} else {
lean_dec_ref(v_a_1504_);
lean_dec_ref_known(v_a_1503_, 1);
lean_dec_ref(v_arg_1488_);
lean_dec_ref(v_arg_1487_);
lean_dec_ref(v_arg_1486_);
lean_dec_ref(v_arg_1485_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1539_ = lean_box(0);
return v___x_1539_;
}
} else {
lean_dec_ref_known(v_a_1503_, 1);
lean_dec_ref(v_arg_1489_);
lean_dec_ref(v_arg_1488_);
lean_dec_ref(v_arg_1487_);
lean_dec_ref(v_arg_1486_);
lean_dec_ref(v_arg_1485_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1540_ = lean_box(0);
return v___x_1540_;
}
} else {
lean_dec_ref(v_a_1503_);
lean_dec_ref(v_arg_1489_);
lean_dec_ref(v_arg_1488_);
lean_dec_ref(v_arg_1487_);
lean_dec_ref(v_arg_1486_);
lean_dec_ref(v_arg_1485_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1541_ = lean_box(0);
return v___x_1541_;
}
} else {
lean_dec_ref(v_arg_1490_);
lean_dec_ref(v_arg_1489_);
lean_dec_ref(v_arg_1488_);
lean_dec_ref(v_arg_1487_);
lean_dec_ref(v_arg_1486_);
lean_dec_ref(v_arg_1485_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1542_ = lean_box(0);
return v___x_1542_;
}
}
}
}
} else {
lean_dec_ref_known(v_pre_1483_, 2);
lean_dec_ref_known(v_pre_1482_, 2);
lean_dec_ref_known(v_declName_1481_, 2);
lean_dec_ref_known(v_fn_1418_, 2);
lean_dec_ref_known(v_fn_1361_, 2);
lean_dec_ref_known(v_fn_1309_, 2);
lean_dec_ref_known(v_fn_1262_, 2);
lean_dec_ref_known(v_fn_1220_, 2);
lean_dec_ref_known(v_fn_1148_, 2);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1543_ = lean_box(0);
return v___x_1543_;
}
} else {
lean_dec(v_pre_1483_);
lean_dec_ref_known(v_pre_1482_, 2);
lean_dec_ref_known(v_declName_1481_, 2);
lean_dec_ref_known(v_fn_1418_, 2);
lean_dec_ref_known(v_fn_1361_, 2);
lean_dec_ref_known(v_fn_1309_, 2);
lean_dec_ref_known(v_fn_1262_, 2);
lean_dec_ref_known(v_fn_1220_, 2);
lean_dec_ref_known(v_fn_1148_, 2);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1544_ = lean_box(0);
return v___x_1544_;
}
} else {
lean_dec(v_pre_1482_);
lean_dec_ref_known(v_declName_1481_, 2);
lean_dec_ref_known(v_fn_1418_, 2);
lean_dec_ref_known(v_fn_1361_, 2);
lean_dec_ref_known(v_fn_1309_, 2);
lean_dec_ref_known(v_fn_1262_, 2);
lean_dec_ref_known(v_fn_1220_, 2);
lean_dec_ref_known(v_fn_1148_, 2);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1545_ = lean_box(0);
return v___x_1545_;
}
} else {
lean_dec(v_declName_1481_);
lean_dec_ref_known(v_fn_1418_, 2);
lean_dec_ref_known(v_fn_1361_, 2);
lean_dec_ref_known(v_fn_1309_, 2);
lean_dec_ref_known(v_fn_1262_, 2);
lean_dec_ref_known(v_fn_1220_, 2);
lean_dec_ref_known(v_fn_1148_, 2);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1147_);
v___x_1546_ = lean_box(0);
return v___x_1546_;
}
                                                                                } else {
                                                                                    lean_dec_ref_known(v_fn_1418_, 2);
                                                                                    lean_dec_ref_known(v_fn_1361_, 2);
                                                                                    lean_dec_ref_known(v_fn_1309_, 2);
                                                                                    lean_dec_ref_known(v_fn_1262_, 2);
                                                                                    lean_dec_ref_known(v_fn_1220_, 2);
                                                                                    lean_dec_ref_known(v_fn_1148_, 2);
                                                                                    lean_dec_ref(
                                                                                        v_arg_1149_,
                                                                                    );
                                                                                    lean_dec_ref(
                                                                                        v_arg_1147_,
                                                                                    );
                                                                                    v___x_1547_ =
                                                                                        lean_box(0);
                                                                                    return v___x_1547_;
                                                                                }
                                                                            }
                                                                            _ => {
                                                                                lean_dec_ref_known(
                                                                                    v_fn_1361_, 2,
                                                                                );
                                                                                lean_dec_ref_known(
                                                                                    v_fn_1309_, 2,
                                                                                );
                                                                                lean_dec_ref_known(
                                                                                    v_fn_1262_, 2,
                                                                                );
                                                                                lean_dec_ref_known(
                                                                                    v_fn_1220_, 2,
                                                                                );
                                                                                lean_dec_ref_known(
                                                                                    v_fn_1148_, 2,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_1149_,
                                                                                );
                                                                                lean_dec_ref(
                                                                                    v_arg_1147_,
                                                                                );
                                                                                v___x_1548_ =
                                                                                    lean_box(0);
                                                                                return v___x_1548_;
                                                                            }
                                                                        }
                                                                    }
                                                                    _ => {
                                                                        lean_dec_ref_known(
                                                                            v_fn_1309_, 2,
                                                                        );
                                                                        lean_dec_ref_known(
                                                                            v_fn_1262_, 2,
                                                                        );
                                                                        lean_dec_ref_known(
                                                                            v_fn_1220_, 2,
                                                                        );
                                                                        lean_dec_ref_known(
                                                                            v_fn_1148_, 2,
                                                                        );
                                                                        lean_dec_ref(v_arg_1149_);
                                                                        lean_dec_ref(v_arg_1147_);
                                                                        v___x_1549_ = lean_box(0);
                                                                        return v___x_1549_;
                                                                    }
                                                                }
                                                            }
                                                            _ => {
                                                                lean_dec_ref_known(v_fn_1262_, 2);
                                                                lean_dec_ref_known(v_fn_1220_, 2);
                                                                lean_dec_ref_known(v_fn_1148_, 2);
                                                                lean_dec_ref(v_arg_1149_);
                                                                lean_dec_ref(v_arg_1147_);
                                                                v___x_1550_ = lean_box(0);
                                                                return v___x_1550_;
                                                            }
                                                        }
                                                    }
                                                    _ => {
                                                        lean_dec_ref_known(v_fn_1220_, 2);
                                                        lean_dec_ref_known(v_fn_1148_, 2);
                                                        lean_dec_ref(v_arg_1149_);
                                                        lean_dec_ref(v_arg_1147_);
                                                        v___x_1551_ = lean_box(0);
                                                        return v___x_1551_;
                                                    }
                                                }
                                            }
                                            _ => {
                                                lean_dec_ref_known(v_fn_1148_, 2);
                                                lean_dec_ref(v_arg_1149_);
                                                lean_dec_ref(v_arg_1147_);
                                                v___x_1552_ = lean_box(0);
                                                return v___x_1552_;
                                            }
                                        }
                                    }
                                    _ => {
                                        lean_dec_ref(v_arg_1149_);
                                        lean_dec_ref(v_fn_1148_);
                                        lean_dec_ref(v_arg_1147_);
                                        v___x_1553_ = lean_box(0);
                                        return v___x_1553_;
                                    }
                                }
                            }
                            4 => {
                                v_declName_1554_ = lean_ctor_get(v_fn_1146_, 0);
                                lean_inc(v_declName_1554_);
                                if lean_obj_tag(v_declName_1554_) == 1 {
                                    v_pre_1555_ = lean_ctor_get(v_declName_1554_, 0);
                                    lean_inc(v_pre_1555_);
                                    if lean_obj_tag(v_pre_1555_) == 1 {
                                        v_pre_1556_ = lean_ctor_get(v_pre_1555_, 0);
                                        lean_inc(v_pre_1556_);
                                        if lean_obj_tag(v_pre_1556_) == 1 {
                                            v_pre_1557_ = lean_ctor_get(v_pre_1556_, 0);
                                            if lean_obj_tag(v_pre_1557_) == 0 {
                                                v_arg_1558_ = lean_ctor_get(v_x_1124_, 1);
                                                lean_inc_ref(v_arg_1558_);
                                                lean_dec_ref_known(v_x_1124_, 2);
                                                v_str_1559_ = lean_ctor_get(v_declName_1554_, 1);
                                                lean_inc_ref(v_str_1559_);
                                                lean_dec_ref_known(v_declName_1554_, 2);
                                                v_str_1560_ = lean_ctor_get(v_pre_1555_, 1);
                                                lean_inc_ref(v_str_1560_);
                                                lean_dec_ref_known(v_pre_1555_, 2);
                                                v_str_1561_ = lean_ctor_get(v_pre_1556_, 1);
                                                lean_inc_ref(v_str_1561_);
                                                lean_dec_ref_known(v_pre_1556_, 2);
                                                v___x_1562_ = l_Lean_Expr_name_x3f___closed__0;
                                                v___x_1563_ =
                                                    lean_string_dec_eq(v_str_1561_, v___x_1562_);
                                                lean_dec_ref(v_str_1561_);
                                                if v___x_1563_ == 0 {
                                                    lean_dec_ref(v_str_1560_);
                                                    lean_dec_ref(v_str_1559_);
                                                    lean_dec_ref(v_arg_1558_);
                                                    v___x_1564_ = lean_box(0);
                                                    return v___x_1564_;
                                                } else {
                                                    v___x_1565_ = l_Lean_Expr_name_x3f___closed__1;
                                                    v___x_1566_ = lean_string_dec_eq(
                                                        v_str_1560_,
                                                        v___x_1565_,
                                                    );
                                                    lean_dec_ref(v_str_1560_);
                                                    if v___x_1566_ == 0 {
                                                        lean_dec_ref(v_str_1559_);
                                                        lean_dec_ref(v_arg_1558_);
                                                        v___x_1567_ = lean_box(0);
                                                        return v___x_1567_;
                                                    } else {
                                                        v___x_1568_ =
                                                            l_Lean_Expr_name_x3f___closed__12;
                                                        v___x_1569_ = lean_string_dec_eq(
                                                            v_str_1559_,
                                                            v___x_1568_,
                                                        );
                                                        lean_dec_ref(v_str_1559_);
                                                        if v___x_1569_ == 0 {
                                                            lean_dec_ref(v_arg_1558_);
                                                            v___x_1570_ = lean_box(0);
                                                            return v___x_1570_;
                                                        } else {
                                                            if lean_obj_tag(v_arg_1558_) == 9 {
                                                                v_a_1571_ =
                                                                    lean_ctor_get(v_arg_1558_, 0);
                                                                lean_inc_ref(v_a_1571_);
                                                                lean_dec_ref_known(v_arg_1558_, 1);
                                                                if lean_obj_tag(v_a_1571_) == 1 {
                                                                    v_val_1572_ =
                                                                        lean_ctor_get(v_a_1571_, 0);
                                                                    v_isSharedCheck_1580_ =
                                                                        (!lean_is_exclusive(
                                                                            v_a_1571_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_1580_ == 0 {
                                                                        v___x_1574_ = v_a_1571_;
                                                                        v_isShared_1575_ =
                                                                            v_isSharedCheck_1580_;
                                                                        state = 20;
                                                                        continue;
                                                                    } else {
                                                                        lean_inc(v_val_1572_);
                                                                        lean_dec(v_a_1571_);
                                                                        v___x_1574_ = lean_box(0);
                                                                        v_isShared_1575_ =
                                                                            v_isSharedCheck_1580_;
                                                                        state = 20;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    lean_dec_ref(v_a_1571_);
                                                                    v___x_1581_ = lean_box(0);
                                                                    return v___x_1581_;
                                                                }
                                                            } else {
                                                                lean_dec_ref(v_arg_1558_);
                                                                v___x_1582_ = lean_box(0);
                                                                return v___x_1582_;
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref_known(v_pre_1556_, 2);
                                                lean_dec_ref_known(v_pre_1555_, 2);
                                                lean_dec_ref_known(v_declName_1554_, 2);
                                                lean_dec_ref_known(v_x_1124_, 2);
                                                v___x_1583_ = lean_box(0);
                                                return v___x_1583_;
                                            }
                                        } else {
                                            lean_dec_ref_known(v_pre_1555_, 2);
                                            lean_dec(v_pre_1556_);
                                            lean_dec_ref_known(v_declName_1554_, 2);
                                            lean_dec_ref_known(v_x_1124_, 2);
                                            v___x_1584_ = lean_box(0);
                                            return v___x_1584_;
                                        }
                                    } else {
                                        lean_dec(v_pre_1555_);
                                        lean_dec_ref_known(v_declName_1554_, 2);
                                        lean_dec_ref_known(v_x_1124_, 2);
                                        v___x_1585_ = lean_box(0);
                                        return v___x_1585_;
                                    }
                                } else {
                                    lean_dec(v_declName_1554_);
                                    lean_dec_ref_known(v_x_1124_, 2);
                                    v___x_1586_ = lean_box(0);
                                    return v___x_1586_;
                                }
                            }
                            _ => {
                                lean_dec_ref_known(v_x_1124_, 2);
                                v___x_1587_ = lean_box(0);
                                return v___x_1587_;
                            }
                        }
                    }
                    _ => {
                        lean_dec_ref(v_x_1124_);
                        v___x_1588_ = lean_box(0);
                        return v___x_1588_;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_1151_) == 0 {
                    lean_dec_ref(v_arg_1149_);
                    v___x_1152_ = lean_box(0);
                    return v___x_1152_;
                } else {
                    v_val_1153_ = lean_ctor_get(v___y_1151_, 0);
                    lean_inc(v_val_1153_);
                    lean_dec_ref_known(v___y_1151_, 1);
                    v___x_1154_ = l_Lean_Expr_name_x3f(v_arg_1149_);
                    if lean_obj_tag(v___x_1154_) == 0 {
                        lean_dec(v_val_1153_);
                        return v___x_1154_;
                    } else {
                        v_val_1155_ = lean_ctor_get(v___x_1154_, 0);
                        v_isSharedCheck_1163_ = (!lean_is_exclusive(v___x_1154_)) as u8;
                        if v_isSharedCheck_1163_ == 0 {
                            v___x_1157_ = v___x_1154_;
                            v_isShared_1158_ = v_isSharedCheck_1163_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_1155_);
                            lean_dec(v___x_1154_);
                            v___x_1157_ = lean_box(0);
                            v_isShared_1158_ = v_isSharedCheck_1163_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_1159_ = l_Lean_Name_num___override(v_val_1155_, v_val_1153_);
                if v_isShared_1158_ == 0 {
                    lean_ctor_set(v___x_1157_, 0, v___x_1159_);
                    v___x_1161_ = v___x_1157_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1159_);
                    v___x_1161_ = v_reuseFailAlloc_1162_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1161_;
            }
            4 => {
                v___x_1191_ = l_Lean_Name_mkStr2(v_val_1186_, v_val_1187_);
                if v_isShared_1190_ == 0 {
                    lean_ctor_set(v___x_1189_, 0, v___x_1191_);
                    v___x_1193_ = v___x_1189_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1191_);
                    v___x_1193_ = v_reuseFailAlloc_1194_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1193_;
            }
            6 => {
                v___x_1209_ = l_Lean_Name_str___override(v_val_1205_, v_val_1203_);
                if v_isShared_1208_ == 0 {
                    lean_ctor_set(v___x_1207_, 0, v___x_1209_);
                    v___x_1211_ = v___x_1207_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1209_);
                    v___x_1211_ = v_reuseFailAlloc_1212_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1211_;
            }
            8 => {
                v___x_1247_ = l_Lean_Name_mkStr3(v_val_1241_, v_val_1242_, v_val_1243_);
                if v_isShared_1246_ == 0 {
                    lean_ctor_set(v___x_1245_, 0, v___x_1247_);
                    v___x_1249_ = v___x_1245_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
                    v___x_1249_ = v_reuseFailAlloc_1250_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1249_;
            }
            10 => {
                v___x_1292_ =
                    l_Lean_Name_mkStr4(v_val_1285_, v_val_1286_, v_val_1287_, v_val_1288_);
                if v_isShared_1291_ == 0 {
                    lean_ctor_set(v___x_1290_, 0, v___x_1292_);
                    v___x_1294_ = v___x_1290_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1292_);
                    v___x_1294_ = v_reuseFailAlloc_1295_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1294_;
            }
            12 => {
                v___x_1342_ = l_Lean_Name_mkStr5(
                    v_val_1334_,
                    v_val_1335_,
                    v_val_1336_,
                    v_val_1337_,
                    v_val_1338_,
                );
                if v_isShared_1341_ == 0 {
                    lean_ctor_set(v___x_1340_, 0, v___x_1342_);
                    v___x_1344_ = v___x_1340_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
                    v___x_1344_ = v_reuseFailAlloc_1345_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1344_;
            }
            14 => {
                v___x_1397_ = l_Lean_Name_mkStr6(
                    v_val_1388_,
                    v_val_1389_,
                    v_val_1390_,
                    v_val_1391_,
                    v_val_1392_,
                    v_val_1393_,
                );
                if v_isShared_1396_ == 0 {
                    lean_ctor_set(v___x_1395_, 0, v___x_1397_);
                    v___x_1399_ = v___x_1395_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
                    v___x_1399_ = v_reuseFailAlloc_1400_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1399_;
            }
            16 => {
                v___x_1457_ = l_Lean_Name_mkStr7(
                    v_val_1447_,
                    v_val_1448_,
                    v_val_1449_,
                    v_val_1450_,
                    v_val_1451_,
                    v_val_1452_,
                    v_val_1453_,
                );
                if v_isShared_1456_ == 0 {
                    lean_ctor_set(v___x_1455_, 0, v___x_1457_);
                    v___x_1459_ = v___x_1455_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1457_);
                    v___x_1459_ = v_reuseFailAlloc_1460_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1459_;
            }
            18 => {
                v___x_1522_ = l_Lean_Name_mkStr8(
                    v_val_1511_,
                    v_val_1512_,
                    v_val_1513_,
                    v_val_1514_,
                    v_val_1515_,
                    v_val_1516_,
                    v_val_1517_,
                    v_val_1518_,
                );
                if v_isShared_1521_ == 0 {
                    lean_ctor_set(v___x_1520_, 0, v___x_1522_);
                    v___x_1524_ = v___x_1520_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1522_);
                    v___x_1524_ = v_reuseFailAlloc_1525_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1524_;
            }
            20 => {
                v___x_1576_ = l_Lean_Name_mkStr1(v_val_1572_);
                if v_isShared_1575_ == 0 {
                    lean_ctor_set(v___x_1574_, 0, v___x_1576_);
                    v___x_1578_ = v___x_1574_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
                    v___x_1578_ = v_reuseFailAlloc_1579_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1578_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_Recognizers(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Environment(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_Recognizers(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_Recognizers(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Environment(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Recognizers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Util_Recognizers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Util_Recognizers(builtin);
}
