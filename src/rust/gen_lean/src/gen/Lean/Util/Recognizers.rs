// Lean compiler output
// Module: Lean.Util.Recognizers
// Imports: Lean.Environment
use crate::ffi::lean_string_dec_eq;
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
pub static l_Lean_Expr_eq_x3f___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Expr_eq_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_eq_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_eq_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Expr_eq_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16122875713692181903 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Expr_eq_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_eq_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_ne_x3f___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Expr_ne_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_ne_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_ne_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Expr_ne_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6695605208187598753 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Expr_ne_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_ne_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_iff_x3f___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Expr_iff_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_iff_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_iff_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Expr_iff_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9917798623386220051 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Expr_iff_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_iff_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_not_x3f___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Expr_not_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_not_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_not_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Expr_not_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16612019923665488825 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Expr_not_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_not_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_and_x3f___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Expr_and_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_and_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_and_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Expr_and_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9743492140944907313 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Expr_and_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_and_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_heq_x3f___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Expr_heq_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_heq_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_heq_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Expr_heq_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13589827700912665667 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Expr_heq_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_heq_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_natAdd_x3f___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Expr_natAdd_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_natAdd_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_natAdd_x3f___closed__1_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Expr_natAdd_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_natAdd_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_Expr_natAdd_x3f___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Expr_natAdd_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11442535297760353691 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Expr_natAdd_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Expr_natAdd_x3f___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Expr_natAdd_x3f___closed__1_value)
                as *mut crate::leanh::LeanObject,
            17073733886952259026 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Expr_natAdd_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_natAdd_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_isIte___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Expr_isIte___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isIte___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_isIte___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Expr_isIte___closed__0_value)
                as *mut crate::leanh::LeanObject,
            18356704233129443855 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Expr_isIte___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isIte___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_isDIte___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [100, 105, 116, 101, 0],
    };
static mut l_Lean_Expr_isDIte___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isDIte___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_isDIte___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Expr_isDIte___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8391571994004792969 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Expr_isDIte___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isDIte___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__0_value:
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
static mut l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__1_value:
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
static mut l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__1_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__2_value_aux_0:
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
            l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        9582258842178272501 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__2_value:
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
            l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__2_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        18135193680607614554 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__3_value:
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
static mut l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__3_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__4_value_aux_0:
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
            l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        9582258842178272501 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__4_value:
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
            l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        8614124190858717794 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_arrayLit_x3f___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [116, 111, 65, 114, 114, 97, 121, 0],
    };
static mut l_Lean_Expr_arrayLit_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_arrayLit_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Expr_arrayLit_x3f___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__0_value
            ) as *mut crate::leanh::LeanObject,
            9582258842178272501 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Expr_arrayLit_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Expr_arrayLit_x3f___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Expr_arrayLit_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8414467900391110369 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Expr_arrayLit_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_arrayLit_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_prod_x3f___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [80, 114, 111, 100, 0],
    };
static mut l_Lean_Expr_prod_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_prod_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_prod_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Expr_prod_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15289851429949568889 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Expr_prod_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_prod_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_name_x3f___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Expr_name_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_name_x3f___closed__1_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [78, 97, 109, 101, 0],
    };
static mut l_Lean_Expr_name_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_name_x3f___closed__2_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Expr_name_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_name_x3f___closed__3_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Expr_name_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_name_x3f___closed__4_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Expr_name_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_name_x3f___closed__5_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [109, 107, 83, 116, 114, 50, 0],
    };
static mut l_Lean_Expr_name_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_name_x3f___closed__6_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [109, 107, 83, 116, 114, 51, 0],
    };
static mut l_Lean_Expr_name_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_name_x3f___closed__7_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [109, 107, 83, 116, 114, 52, 0],
    };
static mut l_Lean_Expr_name_x3f___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_name_x3f___closed__8_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [109, 107, 83, 116, 114, 53, 0],
    };
static mut l_Lean_Expr_name_x3f___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_name_x3f___closed__9_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [109, 107, 83, 116, 114, 54, 0],
    };
static mut l_Lean_Expr_name_x3f___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_name_x3f___closed__10_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [109, 107, 83, 116, 114, 55, 0],
    };
static mut l_Lean_Expr_name_x3f___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_name_x3f___closed__11_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [109, 107, 83, 116, 114, 56, 0],
    };
static mut l_Lean_Expr_name_x3f___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_name_x3f___closed__12_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [109, 107, 83, 116, 114, 49, 0],
    };
static mut l_Lean_Expr_name_x3f___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_name_x3f___closed__12_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Expr_const_x3f(
    mut v_e_795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_795_) == 4 {
        let mut v_declName_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_us_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_declName_796_ = crate::leanh::lean_ctor_get(v_e_795_, 0);
        v_us_797_ = crate::leanh::lean_ctor_get(v_e_795_, 1);
        crate::leanh::lean_inc(v_us_797_);
        crate::leanh::lean_inc(v_declName_796_);
        v___x_798_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_798_, 0, v_declName_796_);
        crate::leanh::lean_ctor_set(v___x_798_, 1, v_us_797_);
        v___x_799_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_799_, 0, v___x_798_);
        return v___x_799_;
    } else {
        let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_800_ = crate::leanh::lean_box(0);
        return v___x_800_;
    }
}
pub unsafe fn l_Lean_Expr_const_x3f___boxed(
    mut v_e_801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_802_ = l_Lean_Expr_const_x3f(v_e_801_);
    crate::leanh::lean_dec_ref(v_e_801_);
    return v_res_802_;
}
pub unsafe fn l_Lean_Expr_app1_x3f(
    mut v_e_803_: *mut crate::leanh::LeanObject,
    mut v_fName_804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: u8 = 0;
    v___x_805_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_806_ = l_Lean_Expr_isAppOfArity(v_e_803_, v_fName_804_, v___x_805_);
    if v___x_806_ == 0 {
        let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_807_ = crate::leanh::lean_box(0);
        return v___x_807_;
    } else {
        let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_808_ = l_Lean_Expr_appArg_x21(v_e_803_);
        v___x_809_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_809_, 0, v___x_808_);
        return v___x_809_;
    }
}
pub unsafe fn l_Lean_Expr_app1_x3f___boxed(
    mut v_e_810_: *mut crate::leanh::LeanObject,
    mut v_fName_811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_812_ = l_Lean_Expr_app1_x3f(v_e_810_, v_fName_811_);
    crate::leanh::lean_dec(v_fName_811_);
    crate::leanh::lean_dec_ref(v_e_810_);
    return v_res_812_;
}
pub unsafe fn l_Lean_Expr_app2_x3f(
    mut v_e_813_: *mut crate::leanh::LeanObject,
    mut v_fName_814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: u8 = 0;
    v___x_815_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_816_ = l_Lean_Expr_isAppOfArity(v_e_813_, v_fName_814_, v___x_815_);
    if v___x_816_ == 0 {
        let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_817_ = crate::leanh::lean_box(0);
        return v___x_817_;
    } else {
        let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_818_ = l_Lean_Expr_appFn_x21(v_e_813_);
        v___x_819_ = l_Lean_Expr_appArg_x21(v___x_818_);
        crate::leanh::lean_dec_ref(v___x_818_);
        v___x_820_ = l_Lean_Expr_appArg_x21(v_e_813_);
        v___x_821_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_821_, 0, v___x_819_);
        crate::leanh::lean_ctor_set(v___x_821_, 1, v___x_820_);
        v___x_822_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_822_, 0, v___x_821_);
        return v___x_822_;
    }
}
pub unsafe fn l_Lean_Expr_app2_x3f___boxed(
    mut v_e_823_: *mut crate::leanh::LeanObject,
    mut v_fName_824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_825_ = l_Lean_Expr_app2_x3f(v_e_823_, v_fName_824_);
    crate::leanh::lean_dec(v_fName_824_);
    crate::leanh::lean_dec_ref(v_e_823_);
    return v_res_825_;
}
pub unsafe fn l_Lean_Expr_app3_x3f(
    mut v_e_826_: *mut crate::leanh::LeanObject,
    mut v_fName_827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: u8 = 0;
    v___x_828_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_829_ = l_Lean_Expr_isAppOfArity(v_e_826_, v_fName_827_, v___x_828_);
    if v___x_829_ == 0 {
        let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_830_ = crate::leanh::lean_box(0);
        return v___x_830_;
    } else {
        let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_831_ = l_Lean_Expr_appFn_x21(v_e_826_);
        v___x_832_ = l_Lean_Expr_appFn_x21(v___x_831_);
        v___x_833_ = l_Lean_Expr_appArg_x21(v___x_832_);
        crate::leanh::lean_dec_ref(v___x_832_);
        v___x_834_ = l_Lean_Expr_appArg_x21(v___x_831_);
        crate::leanh::lean_dec_ref(v___x_831_);
        v___x_835_ = l_Lean_Expr_appArg_x21(v_e_826_);
        v___x_836_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_836_, 0, v___x_834_);
        crate::leanh::lean_ctor_set(v___x_836_, 1, v___x_835_);
        v___x_837_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_837_, 0, v___x_833_);
        crate::leanh::lean_ctor_set(v___x_837_, 1, v___x_836_);
        v___x_838_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_838_, 0, v___x_837_);
        return v___x_838_;
    }
}
pub unsafe fn l_Lean_Expr_app3_x3f___boxed(
    mut v_e_839_: *mut crate::leanh::LeanObject,
    mut v_fName_840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_841_ = l_Lean_Expr_app3_x3f(v_e_839_, v_fName_840_);
    crate::leanh::lean_dec(v_fName_840_);
    crate::leanh::lean_dec_ref(v_e_839_);
    return v_res_841_;
}
pub unsafe fn l_Lean_Expr_app4_x3f(
    mut v_e_842_: *mut crate::leanh::LeanObject,
    mut v_fName_843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: u8 = 0;
    v___x_844_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_845_ = l_Lean_Expr_isAppOfArity(v_e_842_, v_fName_843_, v___x_844_);
    if v___x_845_ == 0 {
        let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_846_ = crate::leanh::lean_box(0);
        return v___x_846_;
    } else {
        let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_847_ = l_Lean_Expr_appFn_x21(v_e_842_);
        v___x_848_ = l_Lean_Expr_appFn_x21(v___x_847_);
        v___x_849_ = l_Lean_Expr_appFn_x21(v___x_848_);
        v___x_850_ = l_Lean_Expr_appArg_x21(v___x_849_);
        crate::leanh::lean_dec_ref(v___x_849_);
        v___x_851_ = l_Lean_Expr_appArg_x21(v___x_848_);
        crate::leanh::lean_dec_ref(v___x_848_);
        v___x_852_ = l_Lean_Expr_appArg_x21(v___x_847_);
        crate::leanh::lean_dec_ref(v___x_847_);
        v___x_853_ = l_Lean_Expr_appArg_x21(v_e_842_);
        v___x_854_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_854_, 0, v___x_852_);
        crate::leanh::lean_ctor_set(v___x_854_, 1, v___x_853_);
        v___x_855_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_855_, 0, v___x_851_);
        crate::leanh::lean_ctor_set(v___x_855_, 1, v___x_854_);
        v___x_856_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_856_, 0, v___x_850_);
        crate::leanh::lean_ctor_set(v___x_856_, 1, v___x_855_);
        v___x_857_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_857_, 0, v___x_856_);
        return v___x_857_;
    }
}
pub unsafe fn l_Lean_Expr_app4_x3f___boxed(
    mut v_e_858_: *mut crate::leanh::LeanObject,
    mut v_fName_859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_860_ = l_Lean_Expr_app4_x3f(v_e_858_, v_fName_859_);
    crate::leanh::lean_dec(v_fName_859_);
    crate::leanh::lean_dec_ref(v_e_858_);
    return v_res_860_;
}
pub unsafe fn l_Lean_Expr_eq_x3f(
    mut v_p_864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: u8 = 0;
    v___x_865_ = l_Lean_Expr_eq_x3f___closed__1;
    v___x_866_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_867_ = l_Lean_Expr_isAppOfArity(v_p_864_, v___x_865_, v___x_866_);
    if v___x_867_ == 0 {
        let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_868_ = crate::leanh::lean_box(0);
        return v___x_868_;
    } else {
        let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_869_ = l_Lean_Expr_appFn_x21(v_p_864_);
        v___x_870_ = l_Lean_Expr_appFn_x21(v___x_869_);
        v___x_871_ = l_Lean_Expr_appArg_x21(v___x_870_);
        crate::leanh::lean_dec_ref(v___x_870_);
        v___x_872_ = l_Lean_Expr_appArg_x21(v___x_869_);
        crate::leanh::lean_dec_ref(v___x_869_);
        v___x_873_ = l_Lean_Expr_appArg_x21(v_p_864_);
        v___x_874_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_874_, 0, v___x_872_);
        crate::leanh::lean_ctor_set(v___x_874_, 1, v___x_873_);
        v___x_875_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_875_, 0, v___x_871_);
        crate::leanh::lean_ctor_set(v___x_875_, 1, v___x_874_);
        v___x_876_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_876_, 0, v___x_875_);
        return v___x_876_;
    }
}
pub unsafe fn l_Lean_Expr_eq_x3f___boxed(
    mut v_p_877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_878_ = l_Lean_Expr_eq_x3f(v_p_877_);
    crate::leanh::lean_dec_ref(v_p_877_);
    return v_res_878_;
}
pub unsafe fn l_Lean_Expr_ne_x3f(
    mut v_p_882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: u8 = 0;
    v___x_883_ = l_Lean_Expr_ne_x3f___closed__1;
    v___x_884_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_885_ = l_Lean_Expr_isAppOfArity(v_p_882_, v___x_883_, v___x_884_);
    if v___x_885_ == 0 {
        let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_886_ = crate::leanh::lean_box(0);
        return v___x_886_;
    } else {
        let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_887_ = l_Lean_Expr_appFn_x21(v_p_882_);
        v___x_888_ = l_Lean_Expr_appFn_x21(v___x_887_);
        v___x_889_ = l_Lean_Expr_appArg_x21(v___x_888_);
        crate::leanh::lean_dec_ref(v___x_888_);
        v___x_890_ = l_Lean_Expr_appArg_x21(v___x_887_);
        crate::leanh::lean_dec_ref(v___x_887_);
        v___x_891_ = l_Lean_Expr_appArg_x21(v_p_882_);
        v___x_892_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_892_, 0, v___x_890_);
        crate::leanh::lean_ctor_set(v___x_892_, 1, v___x_891_);
        v___x_893_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_893_, 0, v___x_889_);
        crate::leanh::lean_ctor_set(v___x_893_, 1, v___x_892_);
        v___x_894_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_894_, 0, v___x_893_);
        return v___x_894_;
    }
}
pub unsafe fn l_Lean_Expr_ne_x3f___boxed(
    mut v_p_895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_896_ = l_Lean_Expr_ne_x3f(v_p_895_);
    crate::leanh::lean_dec_ref(v_p_895_);
    return v_res_896_;
}
pub unsafe fn l_Lean_Expr_iff_x3f(
    mut v_p_900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: u8 = 0;
    v___x_901_ = l_Lean_Expr_iff_x3f___closed__1;
    v___x_902_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_903_ = l_Lean_Expr_isAppOfArity(v_p_900_, v___x_901_, v___x_902_);
    if v___x_903_ == 0 {
        let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_904_ = crate::leanh::lean_box(0);
        return v___x_904_;
    } else {
        let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_905_ = l_Lean_Expr_appFn_x21(v_p_900_);
        v___x_906_ = l_Lean_Expr_appArg_x21(v___x_905_);
        crate::leanh::lean_dec_ref(v___x_905_);
        v___x_907_ = l_Lean_Expr_appArg_x21(v_p_900_);
        v___x_908_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_908_, 0, v___x_906_);
        crate::leanh::lean_ctor_set(v___x_908_, 1, v___x_907_);
        v___x_909_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_909_, 0, v___x_908_);
        return v___x_909_;
    }
}
pub unsafe fn l_Lean_Expr_iff_x3f___boxed(
    mut v_p_910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_911_ = l_Lean_Expr_iff_x3f(v_p_910_);
    crate::leanh::lean_dec_ref(v_p_910_);
    return v_res_911_;
}
pub unsafe fn l_Lean_Expr_eqOrIff_x3f(
    mut v_p_912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: u8 = 0;
    v___x_913_ = l_Lean_Expr_eq_x3f___closed__1;
    v___x_914_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_915_ = l_Lean_Expr_isAppOfArity(v_p_912_, v___x_913_, v___x_914_);
    if v___x_915_ == 0 {
        let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_918_: u8 = 0;
        v___x_916_ = l_Lean_Expr_iff_x3f___closed__1;
        v___x_917_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_918_ = l_Lean_Expr_isAppOfArity(v_p_912_, v___x_916_, v___x_917_);
        if v___x_918_ == 0 {
            let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_919_ = crate::leanh::lean_box(0);
            return v___x_919_;
        } else {
            let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_920_ = l_Lean_Expr_appFn_x21(v_p_912_);
            v___x_921_ = l_Lean_Expr_appArg_x21(v___x_920_);
            crate::leanh::lean_dec_ref(v___x_920_);
            v___x_922_ = l_Lean_Expr_appArg_x21(v_p_912_);
            v___x_923_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_923_, 0, v___x_921_);
            crate::leanh::lean_ctor_set(v___x_923_, 1, v___x_922_);
            v___x_924_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_924_, 0, v___x_923_);
            return v___x_924_;
        }
    } else {
        let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_925_ = l_Lean_Expr_appFn_x21(v_p_912_);
        v___x_926_ = l_Lean_Expr_appArg_x21(v___x_925_);
        crate::leanh::lean_dec_ref(v___x_925_);
        v___x_927_ = l_Lean_Expr_appArg_x21(v_p_912_);
        v___x_928_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_928_, 0, v___x_926_);
        crate::leanh::lean_ctor_set(v___x_928_, 1, v___x_927_);
        v___x_929_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_929_, 0, v___x_928_);
        return v___x_929_;
    }
}
pub unsafe fn l_Lean_Expr_eqOrIff_x3f___boxed(
    mut v_p_930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_931_ = l_Lean_Expr_eqOrIff_x3f(v_p_930_);
    crate::leanh::lean_dec_ref(v_p_930_);
    return v_res_931_;
}
pub unsafe fn l_Lean_Expr_not_x3f(
    mut v_p_935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: u8 = 0;
    v___x_936_ = l_Lean_Expr_not_x3f___closed__1;
    v___x_937_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_938_ = l_Lean_Expr_isAppOfArity(v_p_935_, v___x_936_, v___x_937_);
    if v___x_938_ == 0 {
        let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_939_ = crate::leanh::lean_box(0);
        return v___x_939_;
    } else {
        let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_940_ = l_Lean_Expr_appArg_x21(v_p_935_);
        v___x_941_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_941_, 0, v___x_940_);
        return v___x_941_;
    }
}
pub unsafe fn l_Lean_Expr_not_x3f___boxed(
    mut v_p_942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_943_ = l_Lean_Expr_not_x3f(v_p_942_);
    crate::leanh::lean_dec_ref(v_p_942_);
    return v_res_943_;
}
pub unsafe fn l_Lean_Expr_notNot_x3f(
    mut v_p_944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: u8 = 0;
    v___x_945_ = l_Lean_Expr_not_x3f___closed__1;
    v___x_946_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_947_ = l_Lean_Expr_isAppOfArity(v_p_944_, v___x_945_, v___x_946_);
    if v___x_947_ == 0 {
        let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_948_ = crate::leanh::lean_box(0);
        return v___x_948_;
    } else {
        let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_950_: u8 = 0;
        v___x_949_ = l_Lean_Expr_appArg_x21(v_p_944_);
        v___x_950_ = l_Lean_Expr_isAppOfArity(v___x_949_, v___x_945_, v___x_946_);
        if v___x_950_ == 0 {
            let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_949_);
            v___x_951_ = crate::leanh::lean_box(0);
            return v___x_951_;
        } else {
            let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_952_ = l_Lean_Expr_appArg_x21(v___x_949_);
            crate::leanh::lean_dec_ref(v___x_949_);
            v___x_953_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_953_, 0, v___x_952_);
            return v___x_953_;
        }
    }
}
pub unsafe fn l_Lean_Expr_notNot_x3f___boxed(
    mut v_p_954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_955_ = l_Lean_Expr_notNot_x3f(v_p_954_);
    crate::leanh::lean_dec_ref(v_p_954_);
    return v_res_955_;
}
pub unsafe fn l_Lean_Expr_and_x3f(
    mut v_p_959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: u8 = 0;
    v___x_960_ = l_Lean_Expr_and_x3f___closed__1;
    v___x_961_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_962_ = l_Lean_Expr_isAppOfArity(v_p_959_, v___x_960_, v___x_961_);
    if v___x_962_ == 0 {
        let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_963_ = crate::leanh::lean_box(0);
        return v___x_963_;
    } else {
        let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_964_ = l_Lean_Expr_appFn_x21(v_p_959_);
        v___x_965_ = l_Lean_Expr_appArg_x21(v___x_964_);
        crate::leanh::lean_dec_ref(v___x_964_);
        v___x_966_ = l_Lean_Expr_appArg_x21(v_p_959_);
        v___x_967_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_967_, 0, v___x_965_);
        crate::leanh::lean_ctor_set(v___x_967_, 1, v___x_966_);
        v___x_968_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_968_, 0, v___x_967_);
        return v___x_968_;
    }
}
pub unsafe fn l_Lean_Expr_and_x3f___boxed(
    mut v_p_969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_970_ = l_Lean_Expr_and_x3f(v_p_969_);
    crate::leanh::lean_dec_ref(v_p_969_);
    return v_res_970_;
}
pub unsafe fn l_Lean_Expr_heq_x3f(
    mut v_p_974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: u8 = 0;
    v___x_975_ = l_Lean_Expr_heq_x3f___closed__1;
    v___x_976_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_977_ = l_Lean_Expr_isAppOfArity(v_p_974_, v___x_975_, v___x_976_);
    if v___x_977_ == 0 {
        let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_978_ = crate::leanh::lean_box(0);
        return v___x_978_;
    } else {
        let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_979_ = l_Lean_Expr_appFn_x21(v_p_974_);
        v___x_980_ = l_Lean_Expr_appFn_x21(v___x_979_);
        v___x_981_ = l_Lean_Expr_appFn_x21(v___x_980_);
        v___x_982_ = l_Lean_Expr_appArg_x21(v___x_981_);
        crate::leanh::lean_dec_ref(v___x_981_);
        v___x_983_ = l_Lean_Expr_appArg_x21(v___x_980_);
        crate::leanh::lean_dec_ref(v___x_980_);
        v___x_984_ = l_Lean_Expr_appArg_x21(v___x_979_);
        crate::leanh::lean_dec_ref(v___x_979_);
        v___x_985_ = l_Lean_Expr_appArg_x21(v_p_974_);
        v___x_986_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_986_, 0, v___x_984_);
        crate::leanh::lean_ctor_set(v___x_986_, 1, v___x_985_);
        v___x_987_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_987_, 0, v___x_983_);
        crate::leanh::lean_ctor_set(v___x_987_, 1, v___x_986_);
        v___x_988_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_988_, 0, v___x_982_);
        crate::leanh::lean_ctor_set(v___x_988_, 1, v___x_987_);
        v___x_989_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_989_, 0, v___x_988_);
        return v___x_989_;
    }
}
pub unsafe fn l_Lean_Expr_heq_x3f___boxed(
    mut v_p_990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_991_ = l_Lean_Expr_heq_x3f(v_p_990_);
    crate::leanh::lean_dec_ref(v_p_990_);
    return v_res_991_;
}
pub unsafe fn l_Lean_Expr_natAdd_x3f(
    mut v_e_997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: u8 = 0;
    v___x_998_ = l_Lean_Expr_natAdd_x3f___closed__2;
    v___x_999_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1000_ = l_Lean_Expr_isAppOfArity(v_e_997_, v___x_998_, v___x_999_);
    if v___x_1000_ == 0 {
        let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1001_ = crate::leanh::lean_box(0);
        return v___x_1001_;
    } else {
        let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1002_ = l_Lean_Expr_appFn_x21(v_e_997_);
        v___x_1003_ = l_Lean_Expr_appArg_x21(v___x_1002_);
        crate::leanh::lean_dec_ref(v___x_1002_);
        v___x_1004_ = l_Lean_Expr_appArg_x21(v_e_997_);
        v___x_1005_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1005_, 0, v___x_1003_);
        crate::leanh::lean_ctor_set(v___x_1005_, 1, v___x_1004_);
        v___x_1006_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1006_, 0, v___x_1005_);
        return v___x_1006_;
    }
}
pub unsafe fn l_Lean_Expr_natAdd_x3f___boxed(
    mut v_e_1007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1008_ = l_Lean_Expr_natAdd_x3f(v_e_1007_);
    crate::leanh::lean_dec_ref(v_e_1007_);
    return v_res_1008_;
}
pub unsafe fn l_Lean_Expr_arrow_x3f(
    mut v_x_1009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1009_) == 7 {
        let mut v_binderType_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1012_: u8 = 0;
        v_binderType_1010_ = crate::leanh::lean_ctor_get(v_x_1009_, 1);
        v_body_1011_ = crate::leanh::lean_ctor_get(v_x_1009_, 2);
        v___x_1012_ = l_Lean_Expr_hasLooseBVars(v_body_1011_);
        if v___x_1012_ == 0 {
            let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_body_1011_);
            crate::leanh::lean_inc_ref(v_binderType_1010_);
            v___x_1013_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1013_, 0, v_binderType_1010_);
            crate::leanh::lean_ctor_set(v___x_1013_, 1, v_body_1011_);
            v___x_1014_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1014_, 0, v___x_1013_);
            return v___x_1014_;
        } else {
            let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1015_ = crate::leanh::lean_box(0);
            return v___x_1015_;
        }
    } else {
        let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1016_ = crate::leanh::lean_box(0);
        return v___x_1016_;
    }
}
pub unsafe fn l_Lean_Expr_arrow_x3f___boxed(
    mut v_x_1017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1018_ = l_Lean_Expr_arrow_x3f(v_x_1017_);
    crate::leanh::lean_dec_ref(v_x_1017_);
    return v_res_1018_;
}
pub unsafe fn l_Lean_Expr_isEq(mut v_e_1019_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: u8 = 0;
    v___x_1020_ = l_Lean_Expr_eq_x3f___closed__1;
    v___x_1021_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_1022_ = l_Lean_Expr_isAppOfArity(v_e_1019_, v___x_1020_, v___x_1021_);
    return v___x_1022_;
}
pub unsafe fn l_Lean_Expr_isEq___boxed(
    mut v_e_1023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1024_: u8 = 0;
    let mut v_r_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1024_ = l_Lean_Expr_isEq(v_e_1023_);
    crate::leanh::lean_dec_ref(v_e_1023_);
    v_r_1025_ = crate::leanh::lean_box((v_res_1024_) as usize);
    return v_r_1025_;
}
pub unsafe fn l_Lean_Expr_isHEq(mut v_e_1026_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: u8 = 0;
    v___x_1027_ = l_Lean_Expr_heq_x3f___closed__1;
    v___x_1028_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_1029_ = l_Lean_Expr_isAppOfArity(v_e_1026_, v___x_1027_, v___x_1028_);
    return v___x_1029_;
}
pub unsafe fn l_Lean_Expr_isHEq___boxed(
    mut v_e_1030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1031_: u8 = 0;
    let mut v_r_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1031_ = l_Lean_Expr_isHEq(v_e_1030_);
    crate::leanh::lean_dec_ref(v_e_1030_);
    v_r_1032_ = crate::leanh::lean_box((v_res_1031_) as usize);
    return v_r_1032_;
}
pub unsafe fn l_Lean_Expr_isIte(mut v_e_1036_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: u8 = 0;
    v___x_1037_ = l_Lean_Expr_isIte___closed__1;
    v___x_1038_ = crate::leanh::lean_unsigned_to_nat(5);
    v___x_1039_ = l_Lean_Expr_isAppOfArity(v_e_1036_, v___x_1037_, v___x_1038_);
    return v___x_1039_;
}
pub unsafe fn l_Lean_Expr_isIte___boxed(
    mut v_e_1040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1041_: u8 = 0;
    let mut v_r_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1041_ = l_Lean_Expr_isIte(v_e_1040_);
    crate::leanh::lean_dec_ref(v_e_1040_);
    v_r_1042_ = crate::leanh::lean_box((v_res_1041_) as usize);
    return v_r_1042_;
}
pub unsafe fn l_Lean_Expr_isDIte(mut v_e_1046_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: u8 = 0;
    v___x_1047_ = l_Lean_Expr_isDIte___closed__1;
    v___x_1048_ = crate::leanh::lean_unsigned_to_nat(5);
    v___x_1049_ = l_Lean_Expr_isAppOfArity(v_e_1046_, v___x_1047_, v___x_1048_);
    return v___x_1049_;
}
pub unsafe fn l_Lean_Expr_isDIte___boxed(
    mut v_e_1050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1051_: u8 = 0;
    let mut v_r_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1051_ = l_Lean_Expr_isDIte(v_e_1050_);
    crate::leanh::lean_dec_ref(v_e_1050_);
    v_r_1052_ = crate::leanh::lean_box((v_res_1051_) as usize);
    return v_r_1052_;
}
pub unsafe fn l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop(
    mut v_e_1062_: *mut crate::leanh::LeanObject,
    mut v_acc_1063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: u8 = 0;
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: u8 = 0;
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1064_ =
                    l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__2;
                v___x_1065_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1066_ = l_Lean_Expr_isAppOfArity_x27(v_e_1062_, v___x_1064_, v___x_1065_);
                if v___x_1066_ == 0 {
                    v___x_1067_ =
                        l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop___closed__4;
                    v___x_1068_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1069_ = l_Lean_Expr_isAppOfArity_x27(v_e_1062_, v___x_1067_, v___x_1068_);
                    if v___x_1069_ == 0 {
                        crate::leanh::lean_dec(v_acc_1063_);
                        crate::leanh::lean_dec_ref(v_e_1062_);
                        v___x_1070_ = crate::leanh::lean_box(0);
                        return v___x_1070_;
                    } else {
                        v___x_1071_ = l_Lean_Expr_appArg_x21_x27(v_e_1062_);
                        v___x_1072_ = l_Lean_Expr_appFn_x21_x27(v_e_1062_);
                        crate::leanh::lean_dec_ref(v_e_1062_);
                        v___x_1073_ = l_Lean_Expr_appArg_x21_x27(v___x_1072_);
                        crate::leanh::lean_dec_ref(v___x_1072_);
                        v___x_1074_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1074_, 0, v___x_1073_);
                        crate::leanh::lean_ctor_set(v___x_1074_, 1, v_acc_1063_);
                        v_e_1062_ = v___x_1071_;
                        v_acc_1063_ = v___x_1074_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_1076_ = l_Lean_Expr_appArg_x21_x27(v_e_1062_);
                    crate::leanh::lean_dec_ref(v_e_1062_);
                    v___x_1077_ = l_List_reverse___redArg(v_acc_1063_);
                    v___x_1078_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1078_, 0, v___x_1076_);
                    crate::leanh::lean_ctor_set(v___x_1078_, 1, v___x_1077_);
                    v___x_1079_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1079_, 0, v___x_1078_);
                    return v___x_1079_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_listLit_x3f(
    mut v_e_1080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1081_ = crate::leanh::lean_box(0);
    v___x_1082_ =
        l___private_Lean_Util_Recognizers_0__Lean_Expr_listLit_x3f_loop(v_e_1080_, v___x_1081_);
    return v___x_1082_;
}
pub unsafe fn l_Lean_Expr_arrayLit_x3f(
    mut v_e_1087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: u8 = 0;
    v___x_1088_ = l_Lean_Expr_arrayLit_x3f___closed__1;
    v___x_1089_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1090_ = l_Lean_Expr_isAppOfArity_x27(v_e_1087_, v___x_1088_, v___x_1089_);
    if v___x_1090_ == 0 {
        let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1091_ = crate::leanh::lean_box(0);
        return v___x_1091_;
    } else {
        let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1092_ = l_Lean_Expr_appArg_x21_x27(v_e_1087_);
        v___x_1093_ = l_Lean_Expr_listLit_x3f(v___x_1092_);
        return v___x_1093_;
    }
}
pub unsafe fn l_Lean_Expr_arrayLit_x3f___boxed(
    mut v_e_1094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1095_ = l_Lean_Expr_arrayLit_x3f(v_e_1094_);
    crate::leanh::lean_dec_ref(v_e_1094_);
    return v_res_1095_;
}
pub unsafe fn l_Lean_Expr_prod_x3f(
    mut v_e_1099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: u8 = 0;
    v___x_1100_ = l_Lean_Expr_prod_x3f___closed__1;
    v___x_1101_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1102_ = l_Lean_Expr_isAppOfArity(v_e_1099_, v___x_1100_, v___x_1101_);
    if v___x_1102_ == 0 {
        let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1103_ = crate::leanh::lean_box(0);
        return v___x_1103_;
    } else {
        let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1104_ = l_Lean_Expr_appFn_x21(v_e_1099_);
        v___x_1105_ = l_Lean_Expr_appArg_x21(v___x_1104_);
        crate::leanh::lean_dec_ref(v___x_1104_);
        v___x_1106_ = l_Lean_Expr_appArg_x21(v_e_1099_);
        v___x_1107_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1107_, 0, v___x_1105_);
        crate::leanh::lean_ctor_set(v___x_1107_, 1, v___x_1106_);
        v___x_1108_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1108_, 0, v___x_1107_);
        return v___x_1108_;
    }
}
pub unsafe fn l_Lean_Expr_prod_x3f___boxed(
    mut v_e_1109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1110_ = l_Lean_Expr_prod_x3f(v_e_1109_);
    crate::leanh::lean_dec_ref(v_e_1109_);
    return v_res_1110_;
}
pub unsafe fn l_Lean_Expr_name_x3f(
    mut v_x_1124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: u8 = 0;
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: u8 = 0;
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: u8 = 0;
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1158_: u8 = 0;
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1163_: u8 = 0;
    let mut v_declName_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: u8 = 0;
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: u8 = 0;
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: u8 = 0;
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: u8 = 0;
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1190_: u8 = 0;
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1195_: u8 = 0;
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1208_: u8 = 0;
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1213_: u8 = 0;
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: u8 = 0;
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: u8 = 0;
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: u8 = 0;
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1246_: u8 = 0;
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1251_: u8 = 0;
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: u8 = 0;
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: u8 = 0;
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: u8 = 0;
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1291_: u8 = 0;
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1296_: u8 = 0;
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: u8 = 0;
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: u8 = 0;
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: u8 = 0;
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1341_: u8 = 0;
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1346_: u8 = 0;
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: u8 = 0;
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: u8 = 0;
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: u8 = 0;
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1396_: u8 = 0;
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1401_: u8 = 0;
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: u8 = 0;
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: u8 = 0;
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: u8 = 0;
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1456_: u8 = 0;
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1461_: u8 = 0;
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: u8 = 0;
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: u8 = 0;
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: u8 = 0;
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1521_: u8 = 0;
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1526_: u8 = 0;
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: u8 = 0;
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: u8 = 0;
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: u8 = 0;
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1575_: u8 = 0;
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1580_: u8 = 0;
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match crate::leanh::lean_obj_tag(v_x_1124_) {
                    4 => {
                        v_declName_1125_ = crate::leanh::lean_ctor_get(v_x_1124_, 0);
                        crate::leanh::lean_inc(v_declName_1125_);
                        crate::leanh::lean_dec_ref_known(v_x_1124_, 2);
                        if crate::leanh::lean_obj_tag(v_declName_1125_) == 1 {
                            v_pre_1126_ = crate::leanh::lean_ctor_get(v_declName_1125_, 0);
                            crate::leanh::lean_inc(v_pre_1126_);
                            if crate::leanh::lean_obj_tag(v_pre_1126_) == 1 {
                                v_pre_1127_ = crate::leanh::lean_ctor_get(v_pre_1126_, 0);
                                crate::leanh::lean_inc(v_pre_1127_);
                                if crate::leanh::lean_obj_tag(v_pre_1127_) == 1 {
                                    v_pre_1128_ = crate::leanh::lean_ctor_get(v_pre_1127_, 0);
                                    crate::leanh::lean_inc(v_pre_1128_);
                                    if crate::leanh::lean_obj_tag(v_pre_1128_) == 0 {
                                        v_str_1129_ =
                                            crate::leanh::lean_ctor_get(v_declName_1125_, 1);
                                        crate::leanh::lean_inc_ref(v_str_1129_);
                                        crate::leanh::lean_dec_ref_known(v_declName_1125_, 2);
                                        v_str_1130_ = crate::leanh::lean_ctor_get(v_pre_1126_, 1);
                                        crate::leanh::lean_inc_ref(v_str_1130_);
                                        crate::leanh::lean_dec_ref_known(v_pre_1126_, 2);
                                        v_str_1131_ = crate::leanh::lean_ctor_get(v_pre_1127_, 1);
                                        crate::leanh::lean_inc_ref(v_str_1131_);
                                        crate::leanh::lean_dec_ref_known(v_pre_1127_, 2);
                                        v___x_1132_ = l_Lean_Expr_name_x3f___closed__0;
                                        v___x_1133_ = lean_string_dec_eq(v_str_1131_, v___x_1132_);
                                        crate::leanh::lean_dec_ref(v_str_1131_);
                                        if v___x_1133_ == 0 {
                                            crate::leanh::lean_dec_ref(v_str_1130_);
                                            crate::leanh::lean_dec_ref(v_str_1129_);
                                            v___x_1134_ = crate::leanh::lean_box(0);
                                            return v___x_1134_;
                                        } else {
                                            v___x_1135_ = l_Lean_Expr_name_x3f___closed__1;
                                            v___x_1136_ =
                                                lean_string_dec_eq(v_str_1130_, v___x_1135_);
                                            crate::leanh::lean_dec_ref(v_str_1130_);
                                            if v___x_1136_ == 0 {
                                                crate::leanh::lean_dec_ref(v_str_1129_);
                                                v___x_1137_ = crate::leanh::lean_box(0);
                                                return v___x_1137_;
                                            } else {
                                                v___x_1138_ = l_Lean_Expr_name_x3f___closed__2;
                                                v___x_1139_ =
                                                    lean_string_dec_eq(v_str_1129_, v___x_1138_);
                                                crate::leanh::lean_dec_ref(v_str_1129_);
                                                if v___x_1139_ == 0 {
                                                    v___x_1140_ = crate::leanh::lean_box(0);
                                                    return v___x_1140_;
                                                } else {
                                                    v___x_1141_ = crate::leanh::lean_alloc_ctor(
                                                        1,
                                                        1,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_1141_,
                                                        0,
                                                        v_pre_1128_,
                                                    );
                                                    return v___x_1141_;
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v_pre_1127_, 2);
                                        crate::leanh::lean_dec(v_pre_1128_);
                                        crate::leanh::lean_dec_ref_known(v_pre_1126_, 2);
                                        crate::leanh::lean_dec_ref_known(v_declName_1125_, 2);
                                        v___x_1142_ = crate::leanh::lean_box(0);
                                        return v___x_1142_;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_pre_1127_);
                                    crate::leanh::lean_dec_ref_known(v_pre_1126_, 2);
                                    crate::leanh::lean_dec_ref_known(v_declName_1125_, 2);
                                    v___x_1143_ = crate::leanh::lean_box(0);
                                    return v___x_1143_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_pre_1126_);
                                crate::leanh::lean_dec_ref_known(v_declName_1125_, 2);
                                v___x_1144_ = crate::leanh::lean_box(0);
                                return v___x_1144_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_declName_1125_);
                            v___x_1145_ = crate::leanh::lean_box(0);
                            return v___x_1145_;
                        }
                    }
                    5 => {
                        v_fn_1146_ = crate::leanh::lean_ctor_get(v_x_1124_, 0);
                        match crate::leanh::lean_obj_tag(v_fn_1146_) {
                            5 => {
                                crate::leanh::lean_inc_ref(v_fn_1146_);
                                v_arg_1147_ = crate::leanh::lean_ctor_get(v_x_1124_, 1);
                                crate::leanh::lean_inc_ref(v_arg_1147_);
                                crate::leanh::lean_dec_ref_known(v_x_1124_, 2);
                                v_fn_1148_ = crate::leanh::lean_ctor_get(v_fn_1146_, 0);
                                crate::leanh::lean_inc_ref(v_fn_1148_);
                                v_arg_1149_ = crate::leanh::lean_ctor_get(v_fn_1146_, 1);
                                crate::leanh::lean_inc_ref(v_arg_1149_);
                                crate::leanh::lean_dec_ref_known(v_fn_1146_, 2);
                                match crate::leanh::lean_obj_tag(v_fn_1148_) {
                                    4 => {
                                        v_declName_1164_ =
                                            crate::leanh::lean_ctor_get(v_fn_1148_, 0);
                                        crate::leanh::lean_inc(v_declName_1164_);
                                        crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
                                        if crate::leanh::lean_obj_tag(v_declName_1164_) == 1 {
                                            v_pre_1165_ =
                                                crate::leanh::lean_ctor_get(v_declName_1164_, 0);
                                            crate::leanh::lean_inc(v_pre_1165_);
                                            if crate::leanh::lean_obj_tag(v_pre_1165_) == 1 {
                                                v_pre_1166_ =
                                                    crate::leanh::lean_ctor_get(v_pre_1165_, 0);
                                                crate::leanh::lean_inc(v_pre_1166_);
                                                if crate::leanh::lean_obj_tag(v_pre_1166_) == 1 {
                                                    v_pre_1167_ =
                                                        crate::leanh::lean_ctor_get(v_pre_1166_, 0);
                                                    if crate::leanh::lean_obj_tag(v_pre_1167_) == 0
                                                    {
                                                        v_str_1168_ = crate::leanh::lean_ctor_get(
                                                            v_declName_1164_,
                                                            1,
                                                        );
                                                        crate::leanh::lean_inc_ref(v_str_1168_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_declName_1164_,
                                                            2,
                                                        );
                                                        v_str_1169_ = crate::leanh::lean_ctor_get(
                                                            v_pre_1165_,
                                                            1,
                                                        );
                                                        crate::leanh::lean_inc_ref(v_str_1169_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_pre_1165_,
                                                            2,
                                                        );
                                                        v_str_1170_ = crate::leanh::lean_ctor_get(
                                                            v_pre_1166_,
                                                            1,
                                                        );
                                                        crate::leanh::lean_inc_ref(v_str_1170_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_pre_1166_,
                                                            2,
                                                        );
                                                        v___x_1171_ =
                                                            l_Lean_Expr_name_x3f___closed__0;
                                                        v___x_1172_ = lean_string_dec_eq(
                                                            v_str_1170_,
                                                            v___x_1171_,
                                                        );
                                                        crate::leanh::lean_dec_ref(v_str_1170_);
                                                        if v___x_1172_ == 0 {
                                                            crate::leanh::lean_dec_ref(v_str_1169_);
                                                            crate::leanh::lean_dec_ref(v_str_1168_);
                                                            crate::leanh::lean_dec_ref(v_arg_1149_);
                                                            crate::leanh::lean_dec_ref(v_arg_1147_);
                                                            v___x_1173_ = crate::leanh::lean_box(0);
                                                            return v___x_1173_;
                                                        } else {
                                                            v___x_1174_ =
                                                                l_Lean_Expr_name_x3f___closed__1;
                                                            v___x_1175_ = lean_string_dec_eq(
                                                                v_str_1169_,
                                                                v___x_1174_,
                                                            );
                                                            crate::leanh::lean_dec_ref(v_str_1169_);
                                                            if v___x_1175_ == 0 {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_str_1168_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_1149_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_1147_,
                                                                );
                                                                v___x_1176_ =
                                                                    crate::leanh::lean_box(0);
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
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_str_1168_,
                                                                        );
                                                                        if v___x_1182_ == 0 {
                                                                            crate::leanh::lean_dec_ref(v_arg_1149_);
                                                                            crate::leanh::lean_dec_ref(v_arg_1147_);
                                                                            v___x_1183_ = crate::leanh::lean_box(0);
                                                                            return v___x_1183_;
                                                                        } else {
                                                                            if crate::leanh::lean_obj_tag(v_arg_1149_) == 9 {
v_a_1184_ = crate::leanh::lean_ctor_get(v_arg_1149_, 0);
crate::leanh::lean_inc_ref(v_a_1184_);
crate::leanh::lean_dec_ref_known(v_arg_1149_, 1);
if crate::leanh::lean_obj_tag(v_a_1184_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1147_) == 9 {
v_a_1185_ = crate::leanh::lean_ctor_get(v_arg_1147_, 0);
crate::leanh::lean_inc_ref(v_a_1185_);
crate::leanh::lean_dec_ref_known(v_arg_1147_, 1);
if crate::leanh::lean_obj_tag(v_a_1185_) == 1 {
v_val_1186_ = crate::leanh::lean_ctor_get(v_a_1184_, 0);
crate::leanh::lean_inc_ref(v_val_1186_);
crate::leanh::lean_dec_ref_known(v_a_1184_, 1);
v_val_1187_ = crate::leanh::lean_ctor_get(v_a_1185_, 0);
v_isSharedCheck_1195_ = (!crate::leanh::lean_is_exclusive(v_a_1185_)) as u8;
if v_isSharedCheck_1195_ == 0 {
v___x_1189_ = v_a_1185_;
v_isShared_1190_ = v_isSharedCheck_1195_;
state = 4; continue;
} else {
crate::leanh::lean_inc(v_val_1187_);
crate::leanh::lean_dec(v_a_1185_);
v___x_1189_ = crate::leanh::lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1195_;
state = 4; continue;
}
} else {
crate::leanh::lean_dec_ref(v_a_1185_);
crate::leanh::lean_dec_ref_known(v_a_1184_, 1);
v___x_1196_ = crate::leanh::lean_box(0);
return v___x_1196_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1184_, 1);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1197_ = crate::leanh::lean_box(0);
return v___x_1197_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1184_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1198_ = crate::leanh::lean_box(0);
return v___x_1198_;
}
} else {
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1199_ = crate::leanh::lean_box(0);
return v___x_1199_;
}
                                                                        }
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_str_1168_,
                                                                        );
                                                                        crate::leanh::lean_inc_ref(
                                                                            v_arg_1147_,
                                                                        );
                                                                        v___x_1200_ = l_Lean_Expr_rawNatLit_x3f(v_arg_1147_);
                                                                        if crate::leanh::lean_obj_tag(v___x_1200_) == 0 {
v___x_1201_ = l_Lean_Expr_nat_x3f(v_arg_1147_);
v___y_1151_ = v___x_1201_;
state = 1; continue;
} else {
crate::leanh::lean_dec_ref(v_arg_1147_);
v___y_1151_ = v___x_1200_;
state = 1; continue;
}
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_str_1168_,
                                                                    );
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v_arg_1147_,
                                                                    ) == 9
                                                                    {
                                                                        v_a_1202_ = crate::leanh::lean_ctor_get(v_arg_1147_, 0);
                                                                        crate::leanh::lean_inc_ref(
                                                                            v_a_1202_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v_arg_1147_, 1);
                                                                        if crate::leanh::lean_obj_tag(v_a_1202_) == 1 {
v_val_1203_ = crate::leanh::lean_ctor_get(v_a_1202_, 0);
crate::leanh::lean_inc_ref(v_val_1203_);
crate::leanh::lean_dec_ref_known(v_a_1202_, 1);
v___x_1204_ = l_Lean_Expr_name_x3f(v_arg_1149_);
if crate::leanh::lean_obj_tag(v___x_1204_) == 0 {
crate::leanh::lean_dec_ref(v_val_1203_);
return v___x_1204_;
} else {
v_val_1205_ = crate::leanh::lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1213_ = (!crate::leanh::lean_is_exclusive(v___x_1204_)) as u8;
if v_isSharedCheck_1213_ == 0 {
v___x_1207_ = v___x_1204_;
v_isShared_1208_ = v_isSharedCheck_1213_;
state = 6; continue;
} else {
crate::leanh::lean_inc(v_val_1205_);
crate::leanh::lean_dec(v___x_1204_);
v___x_1207_ = crate::leanh::lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1213_;
state = 6; continue;
}
}
} else {
crate::leanh::lean_dec_ref(v_a_1202_);
crate::leanh::lean_dec_ref(v_arg_1149_);
v___x_1214_ = crate::leanh::lean_box(0);
return v___x_1214_;
}
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1149_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1147_,
                                                                        );
                                                                        v___x_1215_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        return v___x_1215_;
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_pre_1166_,
                                                            2,
                                                        );
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_pre_1165_,
                                                            2,
                                                        );
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_declName_1164_,
                                                            2,
                                                        );
                                                        crate::leanh::lean_dec_ref(v_arg_1149_);
                                                        crate::leanh::lean_dec_ref(v_arg_1147_);
                                                        v___x_1216_ = crate::leanh::lean_box(0);
                                                        return v___x_1216_;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref_known(
                                                        v_pre_1165_,
                                                        2,
                                                    );
                                                    crate::leanh::lean_dec(v_pre_1166_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v_declName_1164_,
                                                        2,
                                                    );
                                                    crate::leanh::lean_dec_ref(v_arg_1149_);
                                                    crate::leanh::lean_dec_ref(v_arg_1147_);
                                                    v___x_1217_ = crate::leanh::lean_box(0);
                                                    return v___x_1217_;
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_pre_1165_);
                                                crate::leanh::lean_dec_ref_known(
                                                    v_declName_1164_,
                                                    2,
                                                );
                                                crate::leanh::lean_dec_ref(v_arg_1149_);
                                                crate::leanh::lean_dec_ref(v_arg_1147_);
                                                v___x_1218_ = crate::leanh::lean_box(0);
                                                return v___x_1218_;
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_declName_1164_);
                                            crate::leanh::lean_dec_ref(v_arg_1149_);
                                            crate::leanh::lean_dec_ref(v_arg_1147_);
                                            v___x_1219_ = crate::leanh::lean_box(0);
                                            return v___x_1219_;
                                        }
                                    }
                                    5 => {
                                        v_fn_1220_ = crate::leanh::lean_ctor_get(v_fn_1148_, 0);
                                        match crate::leanh::lean_obj_tag(v_fn_1220_) {
                                            4 => {
                                                v_declName_1221_ =
                                                    crate::leanh::lean_ctor_get(v_fn_1220_, 0);
                                                crate::leanh::lean_inc(v_declName_1221_);
                                                if crate::leanh::lean_obj_tag(v_declName_1221_) == 1
                                                {
                                                    v_pre_1222_ = crate::leanh::lean_ctor_get(
                                                        v_declName_1221_,
                                                        0,
                                                    );
                                                    crate::leanh::lean_inc(v_pre_1222_);
                                                    if crate::leanh::lean_obj_tag(v_pre_1222_) == 1
                                                    {
                                                        v_pre_1223_ = crate::leanh::lean_ctor_get(
                                                            v_pre_1222_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_pre_1223_);
                                                        if crate::leanh::lean_obj_tag(v_pre_1223_)
                                                            == 1
                                                        {
                                                            v_pre_1224_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_pre_1223_,
                                                                    0,
                                                                );
                                                            if crate::leanh::lean_obj_tag(
                                                                v_pre_1224_,
                                                            ) == 0
                                                            {
                                                                v_arg_1225_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_fn_1148_, 1,
                                                                    );
                                                                crate::leanh::lean_inc_ref(
                                                                    v_arg_1225_,
                                                                );
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_fn_1148_, 2,
                                                                );
                                                                v_str_1226_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_declName_1221_,
                                                                        1,
                                                                    );
                                                                crate::leanh::lean_inc_ref(
                                                                    v_str_1226_,
                                                                );
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_declName_1221_,
                                                                    2,
                                                                );
                                                                v_str_1227_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_pre_1222_,
                                                                        1,
                                                                    );
                                                                crate::leanh::lean_inc_ref(
                                                                    v_str_1227_,
                                                                );
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_pre_1222_,
                                                                    2,
                                                                );
                                                                v_str_1228_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_pre_1223_,
                                                                        1,
                                                                    );
                                                                crate::leanh::lean_inc_ref(
                                                                    v_str_1228_,
                                                                );
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_pre_1223_,
                                                                    2,
                                                                );
                                                                v___x_1229_ = l_Lean_Expr_name_x3f___closed__0;
                                                                v___x_1230_ = lean_string_dec_eq(
                                                                    v_str_1228_,
                                                                    v___x_1229_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_str_1228_,
                                                                );
                                                                if v___x_1230_ == 0 {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_str_1227_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_str_1226_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_1225_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_1149_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_1147_,
                                                                    );
                                                                    v___x_1231_ =
                                                                        crate::leanh::lean_box(0);
                                                                    return v___x_1231_;
                                                                } else {
                                                                    v___x_1232_ = l_Lean_Expr_name_x3f___closed__1;
                                                                    v___x_1233_ =
                                                                        lean_string_dec_eq(
                                                                            v_str_1227_,
                                                                            v___x_1232_,
                                                                        );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_str_1227_,
                                                                    );
                                                                    if v___x_1233_ == 0 {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_str_1226_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1225_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1149_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1147_,
                                                                        );
                                                                        v___x_1234_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        return v___x_1234_;
                                                                    } else {
                                                                        v___x_1235_ = l_Lean_Expr_name_x3f___closed__6;
                                                                        v___x_1236_ =
                                                                            lean_string_dec_eq(
                                                                                v_str_1226_,
                                                                                v___x_1235_,
                                                                            );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_str_1226_,
                                                                        );
                                                                        if v___x_1236_ == 0 {
                                                                            crate::leanh::lean_dec_ref(v_arg_1225_);
                                                                            crate::leanh::lean_dec_ref(v_arg_1149_);
                                                                            crate::leanh::lean_dec_ref(v_arg_1147_);
                                                                            v___x_1237_ = crate::leanh::lean_box(0);
                                                                            return v___x_1237_;
                                                                        } else {
                                                                            if crate::leanh::lean_obj_tag(v_arg_1225_) == 9 {
v_a_1238_ = crate::leanh::lean_ctor_get(v_arg_1225_, 0);
crate::leanh::lean_inc_ref(v_a_1238_);
crate::leanh::lean_dec_ref_known(v_arg_1225_, 1);
if crate::leanh::lean_obj_tag(v_a_1238_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1149_) == 9 {
v_a_1239_ = crate::leanh::lean_ctor_get(v_arg_1149_, 0);
crate::leanh::lean_inc_ref(v_a_1239_);
crate::leanh::lean_dec_ref_known(v_arg_1149_, 1);
if crate::leanh::lean_obj_tag(v_a_1239_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1147_) == 9 {
v_a_1240_ = crate::leanh::lean_ctor_get(v_arg_1147_, 0);
crate::leanh::lean_inc_ref(v_a_1240_);
crate::leanh::lean_dec_ref_known(v_arg_1147_, 1);
if crate::leanh::lean_obj_tag(v_a_1240_) == 1 {
v_val_1241_ = crate::leanh::lean_ctor_get(v_a_1238_, 0);
crate::leanh::lean_inc_ref(v_val_1241_);
crate::leanh::lean_dec_ref_known(v_a_1238_, 1);
v_val_1242_ = crate::leanh::lean_ctor_get(v_a_1239_, 0);
crate::leanh::lean_inc_ref(v_val_1242_);
crate::leanh::lean_dec_ref_known(v_a_1239_, 1);
v_val_1243_ = crate::leanh::lean_ctor_get(v_a_1240_, 0);
v_isSharedCheck_1251_ = (!crate::leanh::lean_is_exclusive(v_a_1240_)) as u8;
if v_isSharedCheck_1251_ == 0 {
v___x_1245_ = v_a_1240_;
v_isShared_1246_ = v_isSharedCheck_1251_;
state = 8; continue;
} else {
crate::leanh::lean_inc(v_val_1243_);
crate::leanh::lean_dec(v_a_1240_);
v___x_1245_ = crate::leanh::lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1251_;
state = 8; continue;
}
} else {
crate::leanh::lean_dec_ref(v_a_1240_);
crate::leanh::lean_dec_ref_known(v_a_1239_, 1);
crate::leanh::lean_dec_ref_known(v_a_1238_, 1);
v___x_1252_ = crate::leanh::lean_box(0);
return v___x_1252_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1239_, 1);
crate::leanh::lean_dec_ref_known(v_a_1238_, 1);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1253_ = crate::leanh::lean_box(0);
return v___x_1253_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1239_);
crate::leanh::lean_dec_ref_known(v_a_1238_, 1);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1254_ = crate::leanh::lean_box(0);
return v___x_1254_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1238_, 1);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1255_ = crate::leanh::lean_box(0);
return v___x_1255_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1238_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1256_ = crate::leanh::lean_box(0);
return v___x_1256_;
}
} else {
crate::leanh::lean_dec_ref(v_arg_1225_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1257_ = crate::leanh::lean_box(0);
return v___x_1257_;
}
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_pre_1223_,
                                                                    2,
                                                                );
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_pre_1222_,
                                                                    2,
                                                                );
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_declName_1221_,
                                                                    2,
                                                                );
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_fn_1148_, 2,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_1149_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_1147_,
                                                                );
                                                                v___x_1258_ =
                                                                    crate::leanh::lean_box(0);
                                                                return v___x_1258_;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec(v_pre_1223_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v_pre_1222_,
                                                                2,
                                                            );
                                                            crate::leanh::lean_dec_ref_known(
                                                                v_declName_1221_,
                                                                2,
                                                            );
                                                            crate::leanh::lean_dec_ref_known(
                                                                v_fn_1148_, 2,
                                                            );
                                                            crate::leanh::lean_dec_ref(v_arg_1149_);
                                                            crate::leanh::lean_dec_ref(v_arg_1147_);
                                                            v___x_1259_ = crate::leanh::lean_box(0);
                                                            return v___x_1259_;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_declName_1221_,
                                                            2,
                                                        );
                                                        crate::leanh::lean_dec(v_pre_1222_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_fn_1148_, 2,
                                                        );
                                                        crate::leanh::lean_dec_ref(v_arg_1149_);
                                                        crate::leanh::lean_dec_ref(v_arg_1147_);
                                                        v___x_1260_ = crate::leanh::lean_box(0);
                                                        return v___x_1260_;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_declName_1221_);
                                                    crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
                                                    crate::leanh::lean_dec_ref(v_arg_1149_);
                                                    crate::leanh::lean_dec_ref(v_arg_1147_);
                                                    v___x_1261_ = crate::leanh::lean_box(0);
                                                    return v___x_1261_;
                                                }
                                            }
                                            5 => {
                                                crate::leanh::lean_inc_ref(v_fn_1220_);
                                                v_fn_1262_ =
                                                    crate::leanh::lean_ctor_get(v_fn_1220_, 0);
                                                match crate::leanh::lean_obj_tag(v_fn_1262_) {
                                                    4 => {
                                                        v_declName_1263_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v_fn_1262_, 0,
                                                            );
                                                        crate::leanh::lean_inc(v_declName_1263_);
                                                        if crate::leanh::lean_obj_tag(
                                                            v_declName_1263_,
                                                        ) == 1
                                                        {
                                                            v_pre_1264_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_declName_1263_,
                                                                    0,
                                                                );
                                                            crate::leanh::lean_inc(v_pre_1264_);
                                                            if crate::leanh::lean_obj_tag(
                                                                v_pre_1264_,
                                                            ) == 1
                                                            {
                                                                v_pre_1265_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_pre_1264_,
                                                                        0,
                                                                    );
                                                                crate::leanh::lean_inc(v_pre_1265_);
                                                                if crate::leanh::lean_obj_tag(
                                                                    v_pre_1265_,
                                                                ) == 1
                                                                {
                                                                    v_pre_1266_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v_pre_1265_,
                                                                            0,
                                                                        );
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v_pre_1266_,
                                                                    ) == 0
                                                                    {
                                                                        v_arg_1267_ = crate::leanh::lean_ctor_get(v_fn_1148_, 1);
                                                                        crate::leanh::lean_inc_ref(
                                                                            v_arg_1267_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
                                                                        v_arg_1268_ = crate::leanh::lean_ctor_get(v_fn_1220_, 1);
                                                                        crate::leanh::lean_inc_ref(
                                                                            v_arg_1268_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
                                                                        v_str_1269_ = crate::leanh::lean_ctor_get(v_declName_1263_, 1);
                                                                        crate::leanh::lean_inc_ref(
                                                                            v_str_1269_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v_declName_1263_, 2);
                                                                        v_str_1270_ = crate::leanh::lean_ctor_get(v_pre_1264_, 1);
                                                                        crate::leanh::lean_inc_ref(
                                                                            v_str_1270_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v_pre_1264_, 2);
                                                                        v_str_1271_ = crate::leanh::lean_ctor_get(v_pre_1265_, 1);
                                                                        crate::leanh::lean_inc_ref(
                                                                            v_str_1271_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v_pre_1265_, 2);
                                                                        v___x_1272_ = l_Lean_Expr_name_x3f___closed__0;
                                                                        v___x_1273_ =
                                                                            lean_string_dec_eq(
                                                                                v_str_1271_,
                                                                                v___x_1272_,
                                                                            );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_str_1271_,
                                                                        );
                                                                        if v___x_1273_ == 0 {
                                                                            crate::leanh::lean_dec_ref(v_str_1270_);
                                                                            crate::leanh::lean_dec_ref(v_str_1269_);
                                                                            crate::leanh::lean_dec_ref(v_arg_1268_);
                                                                            crate::leanh::lean_dec_ref(v_arg_1267_);
                                                                            crate::leanh::lean_dec_ref(v_arg_1149_);
                                                                            crate::leanh::lean_dec_ref(v_arg_1147_);
                                                                            v___x_1274_ = crate::leanh::lean_box(0);
                                                                            return v___x_1274_;
                                                                        } else {
                                                                            v___x_1275_ = l_Lean_Expr_name_x3f___closed__1;
                                                                            v___x_1276_ =
                                                                                lean_string_dec_eq(
                                                                                    v_str_1270_,
                                                                                    v___x_1275_,
                                                                                );
                                                                            crate::leanh::lean_dec_ref(v_str_1270_);
                                                                            if v___x_1276_ == 0 {
                                                                                crate::leanh::lean_dec_ref(v_str_1269_);
                                                                                crate::leanh::lean_dec_ref(v_arg_1268_);
                                                                                crate::leanh::lean_dec_ref(v_arg_1267_);
                                                                                crate::leanh::lean_dec_ref(v_arg_1149_);
                                                                                crate::leanh::lean_dec_ref(v_arg_1147_);
                                                                                v___x_1277_ = crate::leanh::lean_box(0);
                                                                                return v___x_1277_;
                                                                            } else {
                                                                                v___x_1278_ = l_Lean_Expr_name_x3f___closed__7;
                                                                                v___x_1279_ = lean_string_dec_eq(v_str_1269_, v___x_1278_);
                                                                                crate::leanh::lean_dec_ref(v_str_1269_);
                                                                                if v___x_1279_ == 0
                                                                                {
                                                                                    crate::leanh::lean_dec_ref(v_arg_1268_);
                                                                                    crate::leanh::lean_dec_ref(v_arg_1267_);
                                                                                    crate::leanh::lean_dec_ref(v_arg_1149_);
                                                                                    crate::leanh::lean_dec_ref(v_arg_1147_);
                                                                                    v___x_1280_ = crate::leanh::lean_box(0);
                                                                                    return v___x_1280_;
                                                                                } else {
                                                                                    if crate::leanh::lean_obj_tag(v_arg_1268_) == 9 {
v_a_1281_ = crate::leanh::lean_ctor_get(v_arg_1268_, 0);
crate::leanh::lean_inc_ref(v_a_1281_);
crate::leanh::lean_dec_ref_known(v_arg_1268_, 1);
if crate::leanh::lean_obj_tag(v_a_1281_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1267_) == 9 {
v_a_1282_ = crate::leanh::lean_ctor_get(v_arg_1267_, 0);
crate::leanh::lean_inc_ref(v_a_1282_);
crate::leanh::lean_dec_ref_known(v_arg_1267_, 1);
if crate::leanh::lean_obj_tag(v_a_1282_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1149_) == 9 {
v_a_1283_ = crate::leanh::lean_ctor_get(v_arg_1149_, 0);
crate::leanh::lean_inc_ref(v_a_1283_);
crate::leanh::lean_dec_ref_known(v_arg_1149_, 1);
if crate::leanh::lean_obj_tag(v_a_1283_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1147_) == 9 {
v_a_1284_ = crate::leanh::lean_ctor_get(v_arg_1147_, 0);
crate::leanh::lean_inc_ref(v_a_1284_);
crate::leanh::lean_dec_ref_known(v_arg_1147_, 1);
if crate::leanh::lean_obj_tag(v_a_1284_) == 1 {
v_val_1285_ = crate::leanh::lean_ctor_get(v_a_1281_, 0);
crate::leanh::lean_inc_ref(v_val_1285_);
crate::leanh::lean_dec_ref_known(v_a_1281_, 1);
v_val_1286_ = crate::leanh::lean_ctor_get(v_a_1282_, 0);
crate::leanh::lean_inc_ref(v_val_1286_);
crate::leanh::lean_dec_ref_known(v_a_1282_, 1);
v_val_1287_ = crate::leanh::lean_ctor_get(v_a_1283_, 0);
crate::leanh::lean_inc_ref(v_val_1287_);
crate::leanh::lean_dec_ref_known(v_a_1283_, 1);
v_val_1288_ = crate::leanh::lean_ctor_get(v_a_1284_, 0);
v_isSharedCheck_1296_ = (!crate::leanh::lean_is_exclusive(v_a_1284_)) as u8;
if v_isSharedCheck_1296_ == 0 {
v___x_1290_ = v_a_1284_;
v_isShared_1291_ = v_isSharedCheck_1296_;
state = 10; continue;
} else {
crate::leanh::lean_inc(v_val_1288_);
crate::leanh::lean_dec(v_a_1284_);
v___x_1290_ = crate::leanh::lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1296_;
state = 10; continue;
}
} else {
crate::leanh::lean_dec_ref(v_a_1284_);
crate::leanh::lean_dec_ref_known(v_a_1283_, 1);
crate::leanh::lean_dec_ref_known(v_a_1282_, 1);
crate::leanh::lean_dec_ref_known(v_a_1281_, 1);
v___x_1297_ = crate::leanh::lean_box(0);
return v___x_1297_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1283_, 1);
crate::leanh::lean_dec_ref_known(v_a_1282_, 1);
crate::leanh::lean_dec_ref_known(v_a_1281_, 1);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1298_ = crate::leanh::lean_box(0);
return v___x_1298_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1283_);
crate::leanh::lean_dec_ref_known(v_a_1282_, 1);
crate::leanh::lean_dec_ref_known(v_a_1281_, 1);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1299_ = crate::leanh::lean_box(0);
return v___x_1299_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1282_, 1);
crate::leanh::lean_dec_ref_known(v_a_1281_, 1);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1300_ = crate::leanh::lean_box(0);
return v___x_1300_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1282_);
crate::leanh::lean_dec_ref_known(v_a_1281_, 1);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1301_ = crate::leanh::lean_box(0);
return v___x_1301_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1281_, 1);
crate::leanh::lean_dec_ref(v_arg_1267_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1302_ = crate::leanh::lean_box(0);
return v___x_1302_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1281_);
crate::leanh::lean_dec_ref(v_arg_1267_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1303_ = crate::leanh::lean_box(0);
return v___x_1303_;
}
} else {
crate::leanh::lean_dec_ref(v_arg_1268_);
crate::leanh::lean_dec_ref(v_arg_1267_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1304_ = crate::leanh::lean_box(0);
return v___x_1304_;
}
                                                                                }
                                                                            }
                                                                        }
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref_known(v_pre_1265_, 2);
                                                                        crate::leanh::lean_dec_ref_known(v_pre_1264_, 2);
                                                                        crate::leanh::lean_dec_ref_known(v_declName_1263_, 2);
                                                                        crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
                                                                        crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1149_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1147_,
                                                                        );
                                                                        v___x_1305_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        return v___x_1305_;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec(
                                                                        v_pre_1265_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref_known(v_pre_1264_, 2);
                                                                    crate::leanh::lean_dec_ref_known(v_declName_1263_, 2);
                                                                    crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
                                                                    crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_1149_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_1147_,
                                                                    );
                                                                    v___x_1306_ =
                                                                        crate::leanh::lean_box(0);
                                                                    return v___x_1306_;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_declName_1263_,
                                                                    2,
                                                                );
                                                                crate::leanh::lean_dec(v_pre_1264_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_fn_1220_, 2,
                                                                );
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_fn_1148_, 2,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_1149_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_1147_,
                                                                );
                                                                v___x_1307_ =
                                                                    crate::leanh::lean_box(0);
                                                                return v___x_1307_;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec(
                                                                v_declName_1263_,
                                                            );
                                                            crate::leanh::lean_dec_ref_known(
                                                                v_fn_1220_, 2,
                                                            );
                                                            crate::leanh::lean_dec_ref_known(
                                                                v_fn_1148_, 2,
                                                            );
                                                            crate::leanh::lean_dec_ref(v_arg_1149_);
                                                            crate::leanh::lean_dec_ref(v_arg_1147_);
                                                            v___x_1308_ = crate::leanh::lean_box(0);
                                                            return v___x_1308_;
                                                        }
                                                    }
                                                    5 => {
                                                        crate::leanh::lean_inc_ref(v_fn_1262_);
                                                        v_fn_1309_ = crate::leanh::lean_ctor_get(
                                                            v_fn_1262_, 0,
                                                        );
                                                        match crate::leanh::lean_obj_tag(v_fn_1309_)
                                                        {
                                                            4 => {
                                                                v_declName_1310_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_fn_1309_, 0,
                                                                    );
                                                                crate::leanh::lean_inc(
                                                                    v_declName_1310_,
                                                                );
                                                                if crate::leanh::lean_obj_tag(
                                                                    v_declName_1310_,
                                                                ) == 1
                                                                {
                                                                    v_pre_1311_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v_declName_1310_,
                                                                            0,
                                                                        );
                                                                    crate::leanh::lean_inc(
                                                                        v_pre_1311_,
                                                                    );
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v_pre_1311_,
                                                                    ) == 1
                                                                    {
                                                                        v_pre_1312_ = crate::leanh::lean_ctor_get(v_pre_1311_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_pre_1312_,
                                                                        );
                                                                        if crate::leanh::lean_obj_tag(v_pre_1312_) == 1 {
v_pre_1313_ = crate::leanh::lean_ctor_get(v_pre_1312_, 0);
if crate::leanh::lean_obj_tag(v_pre_1313_) == 0 {
v_arg_1314_ = crate::leanh::lean_ctor_get(v_fn_1148_, 1);
crate::leanh::lean_inc_ref(v_arg_1314_);
crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
v_arg_1315_ = crate::leanh::lean_ctor_get(v_fn_1220_, 1);
crate::leanh::lean_inc_ref(v_arg_1315_);
crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
v_arg_1316_ = crate::leanh::lean_ctor_get(v_fn_1262_, 1);
crate::leanh::lean_inc_ref(v_arg_1316_);
crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
v_str_1317_ = crate::leanh::lean_ctor_get(v_declName_1310_, 1);
crate::leanh::lean_inc_ref(v_str_1317_);
crate::leanh::lean_dec_ref_known(v_declName_1310_, 2);
v_str_1318_ = crate::leanh::lean_ctor_get(v_pre_1311_, 1);
crate::leanh::lean_inc_ref(v_str_1318_);
crate::leanh::lean_dec_ref_known(v_pre_1311_, 2);
v_str_1319_ = crate::leanh::lean_ctor_get(v_pre_1312_, 1);
crate::leanh::lean_inc_ref(v_str_1319_);
crate::leanh::lean_dec_ref_known(v_pre_1312_, 2);
v___x_1320_ = l_Lean_Expr_name_x3f___closed__0;
v___x_1321_ = lean_string_dec_eq(v_str_1319_, v___x_1320_);
crate::leanh::lean_dec_ref(v_str_1319_);
if v___x_1321_ == 0 {
crate::leanh::lean_dec_ref(v_str_1318_);
crate::leanh::lean_dec_ref(v_str_1317_);
crate::leanh::lean_dec_ref(v_arg_1316_);
crate::leanh::lean_dec_ref(v_arg_1315_);
crate::leanh::lean_dec_ref(v_arg_1314_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1322_ = crate::leanh::lean_box(0);
return v___x_1322_;
} else {
v___x_1323_ = l_Lean_Expr_name_x3f___closed__1;
v___x_1324_ = lean_string_dec_eq(v_str_1318_, v___x_1323_);
crate::leanh::lean_dec_ref(v_str_1318_);
if v___x_1324_ == 0 {
crate::leanh::lean_dec_ref(v_str_1317_);
crate::leanh::lean_dec_ref(v_arg_1316_);
crate::leanh::lean_dec_ref(v_arg_1315_);
crate::leanh::lean_dec_ref(v_arg_1314_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1325_ = crate::leanh::lean_box(0);
return v___x_1325_;
} else {
v___x_1326_ = l_Lean_Expr_name_x3f___closed__8;
v___x_1327_ = lean_string_dec_eq(v_str_1317_, v___x_1326_);
crate::leanh::lean_dec_ref(v_str_1317_);
if v___x_1327_ == 0 {
crate::leanh::lean_dec_ref(v_arg_1316_);
crate::leanh::lean_dec_ref(v_arg_1315_);
crate::leanh::lean_dec_ref(v_arg_1314_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1328_ = crate::leanh::lean_box(0);
return v___x_1328_;
} else {
if crate::leanh::lean_obj_tag(v_arg_1316_) == 9 {
v_a_1329_ = crate::leanh::lean_ctor_get(v_arg_1316_, 0);
crate::leanh::lean_inc_ref(v_a_1329_);
crate::leanh::lean_dec_ref_known(v_arg_1316_, 1);
if crate::leanh::lean_obj_tag(v_a_1329_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1315_) == 9 {
v_a_1330_ = crate::leanh::lean_ctor_get(v_arg_1315_, 0);
crate::leanh::lean_inc_ref(v_a_1330_);
crate::leanh::lean_dec_ref_known(v_arg_1315_, 1);
if crate::leanh::lean_obj_tag(v_a_1330_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1314_) == 9 {
v_a_1331_ = crate::leanh::lean_ctor_get(v_arg_1314_, 0);
crate::leanh::lean_inc_ref(v_a_1331_);
crate::leanh::lean_dec_ref_known(v_arg_1314_, 1);
if crate::leanh::lean_obj_tag(v_a_1331_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1149_) == 9 {
v_a_1332_ = crate::leanh::lean_ctor_get(v_arg_1149_, 0);
crate::leanh::lean_inc_ref(v_a_1332_);
crate::leanh::lean_dec_ref_known(v_arg_1149_, 1);
if crate::leanh::lean_obj_tag(v_a_1332_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1147_) == 9 {
v_a_1333_ = crate::leanh::lean_ctor_get(v_arg_1147_, 0);
crate::leanh::lean_inc_ref(v_a_1333_);
crate::leanh::lean_dec_ref_known(v_arg_1147_, 1);
if crate::leanh::lean_obj_tag(v_a_1333_) == 1 {
v_val_1334_ = crate::leanh::lean_ctor_get(v_a_1329_, 0);
crate::leanh::lean_inc_ref(v_val_1334_);
crate::leanh::lean_dec_ref_known(v_a_1329_, 1);
v_val_1335_ = crate::leanh::lean_ctor_get(v_a_1330_, 0);
crate::leanh::lean_inc_ref(v_val_1335_);
crate::leanh::lean_dec_ref_known(v_a_1330_, 1);
v_val_1336_ = crate::leanh::lean_ctor_get(v_a_1331_, 0);
crate::leanh::lean_inc_ref(v_val_1336_);
crate::leanh::lean_dec_ref_known(v_a_1331_, 1);
v_val_1337_ = crate::leanh::lean_ctor_get(v_a_1332_, 0);
crate::leanh::lean_inc_ref(v_val_1337_);
crate::leanh::lean_dec_ref_known(v_a_1332_, 1);
v_val_1338_ = crate::leanh::lean_ctor_get(v_a_1333_, 0);
v_isSharedCheck_1346_ = (!crate::leanh::lean_is_exclusive(v_a_1333_)) as u8;
if v_isSharedCheck_1346_ == 0 {
v___x_1340_ = v_a_1333_;
v_isShared_1341_ = v_isSharedCheck_1346_;
state = 12; continue;
} else {
crate::leanh::lean_inc(v_val_1338_);
crate::leanh::lean_dec(v_a_1333_);
v___x_1340_ = crate::leanh::lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1346_;
state = 12; continue;
}
} else {
crate::leanh::lean_dec_ref(v_a_1333_);
crate::leanh::lean_dec_ref_known(v_a_1332_, 1);
crate::leanh::lean_dec_ref_known(v_a_1331_, 1);
crate::leanh::lean_dec_ref_known(v_a_1330_, 1);
crate::leanh::lean_dec_ref_known(v_a_1329_, 1);
v___x_1347_ = crate::leanh::lean_box(0);
return v___x_1347_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1332_, 1);
crate::leanh::lean_dec_ref_known(v_a_1331_, 1);
crate::leanh::lean_dec_ref_known(v_a_1330_, 1);
crate::leanh::lean_dec_ref_known(v_a_1329_, 1);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1348_ = crate::leanh::lean_box(0);
return v___x_1348_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1332_);
crate::leanh::lean_dec_ref_known(v_a_1331_, 1);
crate::leanh::lean_dec_ref_known(v_a_1330_, 1);
crate::leanh::lean_dec_ref_known(v_a_1329_, 1);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1349_ = crate::leanh::lean_box(0);
return v___x_1349_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1331_, 1);
crate::leanh::lean_dec_ref_known(v_a_1330_, 1);
crate::leanh::lean_dec_ref_known(v_a_1329_, 1);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1350_ = crate::leanh::lean_box(0);
return v___x_1350_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1331_);
crate::leanh::lean_dec_ref_known(v_a_1330_, 1);
crate::leanh::lean_dec_ref_known(v_a_1329_, 1);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1351_ = crate::leanh::lean_box(0);
return v___x_1351_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1330_, 1);
crate::leanh::lean_dec_ref_known(v_a_1329_, 1);
crate::leanh::lean_dec_ref(v_arg_1314_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1352_ = crate::leanh::lean_box(0);
return v___x_1352_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1330_);
crate::leanh::lean_dec_ref_known(v_a_1329_, 1);
crate::leanh::lean_dec_ref(v_arg_1314_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1353_ = crate::leanh::lean_box(0);
return v___x_1353_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1329_, 1);
crate::leanh::lean_dec_ref(v_arg_1315_);
crate::leanh::lean_dec_ref(v_arg_1314_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1354_ = crate::leanh::lean_box(0);
return v___x_1354_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1329_);
crate::leanh::lean_dec_ref(v_arg_1315_);
crate::leanh::lean_dec_ref(v_arg_1314_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1355_ = crate::leanh::lean_box(0);
return v___x_1355_;
}
} else {
crate::leanh::lean_dec_ref(v_arg_1316_);
crate::leanh::lean_dec_ref(v_arg_1315_);
crate::leanh::lean_dec_ref(v_arg_1314_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1356_ = crate::leanh::lean_box(0);
return v___x_1356_;
}
}
}
}
} else {
crate::leanh::lean_dec_ref_known(v_pre_1312_, 2);
crate::leanh::lean_dec_ref_known(v_pre_1311_, 2);
crate::leanh::lean_dec_ref_known(v_declName_1310_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1357_ = crate::leanh::lean_box(0);
return v___x_1357_;
}
} else {
crate::leanh::lean_dec(v_pre_1312_);
crate::leanh::lean_dec_ref_known(v_pre_1311_, 2);
crate::leanh::lean_dec_ref_known(v_declName_1310_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1358_ = crate::leanh::lean_box(0);
return v___x_1358_;
}
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref_known(v_declName_1310_, 2);
                                                                        crate::leanh::lean_dec(
                                                                            v_pre_1311_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
                                                                        crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
                                                                        crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1149_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1147_,
                                                                        );
                                                                        v___x_1359_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        return v___x_1359_;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec(
                                                                        v_declName_1310_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
                                                                    crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
                                                                    crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_1149_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_1147_,
                                                                    );
                                                                    v___x_1360_ =
                                                                        crate::leanh::lean_box(0);
                                                                    return v___x_1360_;
                                                                }
                                                            }
                                                            5 => {
                                                                crate::leanh::lean_inc_ref(
                                                                    v_fn_1309_,
                                                                );
                                                                v_fn_1361_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_fn_1309_, 0,
                                                                    );
                                                                match crate::leanh::lean_obj_tag(
                                                                    v_fn_1361_,
                                                                ) {
                                                                    4 => {
                                                                        v_declName_1362_ = crate::leanh::lean_ctor_get(v_fn_1361_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_declName_1362_,
                                                                        );
                                                                        if crate::leanh::lean_obj_tag(v_declName_1362_) == 1 {
v_pre_1363_ = crate::leanh::lean_ctor_get(v_declName_1362_, 0);
crate::leanh::lean_inc(v_pre_1363_);
if crate::leanh::lean_obj_tag(v_pre_1363_) == 1 {
v_pre_1364_ = crate::leanh::lean_ctor_get(v_pre_1363_, 0);
crate::leanh::lean_inc(v_pre_1364_);
if crate::leanh::lean_obj_tag(v_pre_1364_) == 1 {
v_pre_1365_ = crate::leanh::lean_ctor_get(v_pre_1364_, 0);
if crate::leanh::lean_obj_tag(v_pre_1365_) == 0 {
v_arg_1366_ = crate::leanh::lean_ctor_get(v_fn_1148_, 1);
crate::leanh::lean_inc_ref(v_arg_1366_);
crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
v_arg_1367_ = crate::leanh::lean_ctor_get(v_fn_1220_, 1);
crate::leanh::lean_inc_ref(v_arg_1367_);
crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
v_arg_1368_ = crate::leanh::lean_ctor_get(v_fn_1262_, 1);
crate::leanh::lean_inc_ref(v_arg_1368_);
crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
v_arg_1369_ = crate::leanh::lean_ctor_get(v_fn_1309_, 1);
crate::leanh::lean_inc_ref(v_arg_1369_);
crate::leanh::lean_dec_ref_known(v_fn_1309_, 2);
v_str_1370_ = crate::leanh::lean_ctor_get(v_declName_1362_, 1);
crate::leanh::lean_inc_ref(v_str_1370_);
crate::leanh::lean_dec_ref_known(v_declName_1362_, 2);
v_str_1371_ = crate::leanh::lean_ctor_get(v_pre_1363_, 1);
crate::leanh::lean_inc_ref(v_str_1371_);
crate::leanh::lean_dec_ref_known(v_pre_1363_, 2);
v_str_1372_ = crate::leanh::lean_ctor_get(v_pre_1364_, 1);
crate::leanh::lean_inc_ref(v_str_1372_);
crate::leanh::lean_dec_ref_known(v_pre_1364_, 2);
v___x_1373_ = l_Lean_Expr_name_x3f___closed__0;
v___x_1374_ = lean_string_dec_eq(v_str_1372_, v___x_1373_);
crate::leanh::lean_dec_ref(v_str_1372_);
if v___x_1374_ == 0 {
crate::leanh::lean_dec_ref(v_str_1371_);
crate::leanh::lean_dec_ref(v_str_1370_);
crate::leanh::lean_dec_ref(v_arg_1369_);
crate::leanh::lean_dec_ref(v_arg_1368_);
crate::leanh::lean_dec_ref(v_arg_1367_);
crate::leanh::lean_dec_ref(v_arg_1366_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1375_ = crate::leanh::lean_box(0);
return v___x_1375_;
} else {
v___x_1376_ = l_Lean_Expr_name_x3f___closed__1;
v___x_1377_ = lean_string_dec_eq(v_str_1371_, v___x_1376_);
crate::leanh::lean_dec_ref(v_str_1371_);
if v___x_1377_ == 0 {
crate::leanh::lean_dec_ref(v_str_1370_);
crate::leanh::lean_dec_ref(v_arg_1369_);
crate::leanh::lean_dec_ref(v_arg_1368_);
crate::leanh::lean_dec_ref(v_arg_1367_);
crate::leanh::lean_dec_ref(v_arg_1366_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1378_ = crate::leanh::lean_box(0);
return v___x_1378_;
} else {
v___x_1379_ = l_Lean_Expr_name_x3f___closed__9;
v___x_1380_ = lean_string_dec_eq(v_str_1370_, v___x_1379_);
crate::leanh::lean_dec_ref(v_str_1370_);
if v___x_1380_ == 0 {
crate::leanh::lean_dec_ref(v_arg_1369_);
crate::leanh::lean_dec_ref(v_arg_1368_);
crate::leanh::lean_dec_ref(v_arg_1367_);
crate::leanh::lean_dec_ref(v_arg_1366_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1381_ = crate::leanh::lean_box(0);
return v___x_1381_;
} else {
if crate::leanh::lean_obj_tag(v_arg_1369_) == 9 {
v_a_1382_ = crate::leanh::lean_ctor_get(v_arg_1369_, 0);
crate::leanh::lean_inc_ref(v_a_1382_);
crate::leanh::lean_dec_ref_known(v_arg_1369_, 1);
if crate::leanh::lean_obj_tag(v_a_1382_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1368_) == 9 {
v_a_1383_ = crate::leanh::lean_ctor_get(v_arg_1368_, 0);
crate::leanh::lean_inc_ref(v_a_1383_);
crate::leanh::lean_dec_ref_known(v_arg_1368_, 1);
if crate::leanh::lean_obj_tag(v_a_1383_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1367_) == 9 {
v_a_1384_ = crate::leanh::lean_ctor_get(v_arg_1367_, 0);
crate::leanh::lean_inc_ref(v_a_1384_);
crate::leanh::lean_dec_ref_known(v_arg_1367_, 1);
if crate::leanh::lean_obj_tag(v_a_1384_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1366_) == 9 {
v_a_1385_ = crate::leanh::lean_ctor_get(v_arg_1366_, 0);
crate::leanh::lean_inc_ref(v_a_1385_);
crate::leanh::lean_dec_ref_known(v_arg_1366_, 1);
if crate::leanh::lean_obj_tag(v_a_1385_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1149_) == 9 {
v_a_1386_ = crate::leanh::lean_ctor_get(v_arg_1149_, 0);
crate::leanh::lean_inc_ref(v_a_1386_);
crate::leanh::lean_dec_ref_known(v_arg_1149_, 1);
if crate::leanh::lean_obj_tag(v_a_1386_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1147_) == 9 {
v_a_1387_ = crate::leanh::lean_ctor_get(v_arg_1147_, 0);
crate::leanh::lean_inc_ref(v_a_1387_);
crate::leanh::lean_dec_ref_known(v_arg_1147_, 1);
if crate::leanh::lean_obj_tag(v_a_1387_) == 1 {
v_val_1388_ = crate::leanh::lean_ctor_get(v_a_1382_, 0);
crate::leanh::lean_inc_ref(v_val_1388_);
crate::leanh::lean_dec_ref_known(v_a_1382_, 1);
v_val_1389_ = crate::leanh::lean_ctor_get(v_a_1383_, 0);
crate::leanh::lean_inc_ref(v_val_1389_);
crate::leanh::lean_dec_ref_known(v_a_1383_, 1);
v_val_1390_ = crate::leanh::lean_ctor_get(v_a_1384_, 0);
crate::leanh::lean_inc_ref(v_val_1390_);
crate::leanh::lean_dec_ref_known(v_a_1384_, 1);
v_val_1391_ = crate::leanh::lean_ctor_get(v_a_1385_, 0);
crate::leanh::lean_inc_ref(v_val_1391_);
crate::leanh::lean_dec_ref_known(v_a_1385_, 1);
v_val_1392_ = crate::leanh::lean_ctor_get(v_a_1386_, 0);
crate::leanh::lean_inc_ref(v_val_1392_);
crate::leanh::lean_dec_ref_known(v_a_1386_, 1);
v_val_1393_ = crate::leanh::lean_ctor_get(v_a_1387_, 0);
v_isSharedCheck_1401_ = (!crate::leanh::lean_is_exclusive(v_a_1387_)) as u8;
if v_isSharedCheck_1401_ == 0 {
v___x_1395_ = v_a_1387_;
v_isShared_1396_ = v_isSharedCheck_1401_;
state = 14; continue;
} else {
crate::leanh::lean_inc(v_val_1393_);
crate::leanh::lean_dec(v_a_1387_);
v___x_1395_ = crate::leanh::lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1401_;
state = 14; continue;
}
} else {
crate::leanh::lean_dec_ref(v_a_1387_);
crate::leanh::lean_dec_ref_known(v_a_1386_, 1);
crate::leanh::lean_dec_ref_known(v_a_1385_, 1);
crate::leanh::lean_dec_ref_known(v_a_1384_, 1);
crate::leanh::lean_dec_ref_known(v_a_1383_, 1);
crate::leanh::lean_dec_ref_known(v_a_1382_, 1);
v___x_1402_ = crate::leanh::lean_box(0);
return v___x_1402_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1386_, 1);
crate::leanh::lean_dec_ref_known(v_a_1385_, 1);
crate::leanh::lean_dec_ref_known(v_a_1384_, 1);
crate::leanh::lean_dec_ref_known(v_a_1383_, 1);
crate::leanh::lean_dec_ref_known(v_a_1382_, 1);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1403_ = crate::leanh::lean_box(0);
return v___x_1403_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1386_);
crate::leanh::lean_dec_ref_known(v_a_1385_, 1);
crate::leanh::lean_dec_ref_known(v_a_1384_, 1);
crate::leanh::lean_dec_ref_known(v_a_1383_, 1);
crate::leanh::lean_dec_ref_known(v_a_1382_, 1);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1404_ = crate::leanh::lean_box(0);
return v___x_1404_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1385_, 1);
crate::leanh::lean_dec_ref_known(v_a_1384_, 1);
crate::leanh::lean_dec_ref_known(v_a_1383_, 1);
crate::leanh::lean_dec_ref_known(v_a_1382_, 1);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1405_ = crate::leanh::lean_box(0);
return v___x_1405_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1385_);
crate::leanh::lean_dec_ref_known(v_a_1384_, 1);
crate::leanh::lean_dec_ref_known(v_a_1383_, 1);
crate::leanh::lean_dec_ref_known(v_a_1382_, 1);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1406_ = crate::leanh::lean_box(0);
return v___x_1406_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1384_, 1);
crate::leanh::lean_dec_ref_known(v_a_1383_, 1);
crate::leanh::lean_dec_ref_known(v_a_1382_, 1);
crate::leanh::lean_dec_ref(v_arg_1366_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1407_ = crate::leanh::lean_box(0);
return v___x_1407_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1384_);
crate::leanh::lean_dec_ref_known(v_a_1383_, 1);
crate::leanh::lean_dec_ref_known(v_a_1382_, 1);
crate::leanh::lean_dec_ref(v_arg_1366_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1408_ = crate::leanh::lean_box(0);
return v___x_1408_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1383_, 1);
crate::leanh::lean_dec_ref_known(v_a_1382_, 1);
crate::leanh::lean_dec_ref(v_arg_1367_);
crate::leanh::lean_dec_ref(v_arg_1366_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1409_ = crate::leanh::lean_box(0);
return v___x_1409_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1383_);
crate::leanh::lean_dec_ref_known(v_a_1382_, 1);
crate::leanh::lean_dec_ref(v_arg_1367_);
crate::leanh::lean_dec_ref(v_arg_1366_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1410_ = crate::leanh::lean_box(0);
return v___x_1410_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1382_, 1);
crate::leanh::lean_dec_ref(v_arg_1368_);
crate::leanh::lean_dec_ref(v_arg_1367_);
crate::leanh::lean_dec_ref(v_arg_1366_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1411_ = crate::leanh::lean_box(0);
return v___x_1411_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1382_);
crate::leanh::lean_dec_ref(v_arg_1368_);
crate::leanh::lean_dec_ref(v_arg_1367_);
crate::leanh::lean_dec_ref(v_arg_1366_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1412_ = crate::leanh::lean_box(0);
return v___x_1412_;
}
} else {
crate::leanh::lean_dec_ref(v_arg_1369_);
crate::leanh::lean_dec_ref(v_arg_1368_);
crate::leanh::lean_dec_ref(v_arg_1367_);
crate::leanh::lean_dec_ref(v_arg_1366_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1413_ = crate::leanh::lean_box(0);
return v___x_1413_;
}
}
}
}
} else {
crate::leanh::lean_dec_ref_known(v_pre_1364_, 2);
crate::leanh::lean_dec_ref_known(v_pre_1363_, 2);
crate::leanh::lean_dec_ref_known(v_declName_1362_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1309_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1414_ = crate::leanh::lean_box(0);
return v___x_1414_;
}
} else {
crate::leanh::lean_dec_ref_known(v_pre_1363_, 2);
crate::leanh::lean_dec(v_pre_1364_);
crate::leanh::lean_dec_ref_known(v_declName_1362_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1309_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1415_ = crate::leanh::lean_box(0);
return v___x_1415_;
}
} else {
crate::leanh::lean_dec_ref_known(v_declName_1362_, 2);
crate::leanh::lean_dec(v_pre_1363_);
crate::leanh::lean_dec_ref_known(v_fn_1309_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1416_ = crate::leanh::lean_box(0);
return v___x_1416_;
}
} else {
crate::leanh::lean_dec(v_declName_1362_);
crate::leanh::lean_dec_ref_known(v_fn_1309_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1417_ = crate::leanh::lean_box(0);
return v___x_1417_;
}
                                                                    }
                                                                    5 => {
                                                                        crate::leanh::lean_inc_ref(
                                                                            v_fn_1361_,
                                                                        );
                                                                        v_fn_1418_ = crate::leanh::lean_ctor_get(v_fn_1361_, 0);
                                                                        match crate::leanh::lean_obj_tag(v_fn_1418_)
{
4 => {
v_declName_1419_ = crate::leanh::lean_ctor_get(v_fn_1418_, 0);
crate::leanh::lean_inc(v_declName_1419_);
if crate::leanh::lean_obj_tag(v_declName_1419_) == 1 {
v_pre_1420_ = crate::leanh::lean_ctor_get(v_declName_1419_, 0);
crate::leanh::lean_inc(v_pre_1420_);
if crate::leanh::lean_obj_tag(v_pre_1420_) == 1 {
v_pre_1421_ = crate::leanh::lean_ctor_get(v_pre_1420_, 0);
crate::leanh::lean_inc(v_pre_1421_);
if crate::leanh::lean_obj_tag(v_pre_1421_) == 1 {
v_pre_1422_ = crate::leanh::lean_ctor_get(v_pre_1421_, 0);
if crate::leanh::lean_obj_tag(v_pre_1422_) == 0 {
v_arg_1423_ = crate::leanh::lean_ctor_get(v_fn_1148_, 1);
crate::leanh::lean_inc_ref(v_arg_1423_);
crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
v_arg_1424_ = crate::leanh::lean_ctor_get(v_fn_1220_, 1);
crate::leanh::lean_inc_ref(v_arg_1424_);
crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
v_arg_1425_ = crate::leanh::lean_ctor_get(v_fn_1262_, 1);
crate::leanh::lean_inc_ref(v_arg_1425_);
crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
v_arg_1426_ = crate::leanh::lean_ctor_get(v_fn_1309_, 1);
crate::leanh::lean_inc_ref(v_arg_1426_);
crate::leanh::lean_dec_ref_known(v_fn_1309_, 2);
v_arg_1427_ = crate::leanh::lean_ctor_get(v_fn_1361_, 1);
crate::leanh::lean_inc_ref(v_arg_1427_);
crate::leanh::lean_dec_ref_known(v_fn_1361_, 2);
v_str_1428_ = crate::leanh::lean_ctor_get(v_declName_1419_, 1);
crate::leanh::lean_inc_ref(v_str_1428_);
crate::leanh::lean_dec_ref_known(v_declName_1419_, 2);
v_str_1429_ = crate::leanh::lean_ctor_get(v_pre_1420_, 1);
crate::leanh::lean_inc_ref(v_str_1429_);
crate::leanh::lean_dec_ref_known(v_pre_1420_, 2);
v_str_1430_ = crate::leanh::lean_ctor_get(v_pre_1421_, 1);
crate::leanh::lean_inc_ref(v_str_1430_);
crate::leanh::lean_dec_ref_known(v_pre_1421_, 2);
v___x_1431_ = l_Lean_Expr_name_x3f___closed__0;
v___x_1432_ = lean_string_dec_eq(v_str_1430_, v___x_1431_);
crate::leanh::lean_dec_ref(v_str_1430_);
if v___x_1432_ == 0 {
crate::leanh::lean_dec_ref(v_str_1429_);
crate::leanh::lean_dec_ref(v_str_1428_);
crate::leanh::lean_dec_ref(v_arg_1427_);
crate::leanh::lean_dec_ref(v_arg_1426_);
crate::leanh::lean_dec_ref(v_arg_1425_);
crate::leanh::lean_dec_ref(v_arg_1424_);
crate::leanh::lean_dec_ref(v_arg_1423_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1433_ = crate::leanh::lean_box(0);
return v___x_1433_;
} else {
v___x_1434_ = l_Lean_Expr_name_x3f___closed__1;
v___x_1435_ = lean_string_dec_eq(v_str_1429_, v___x_1434_);
crate::leanh::lean_dec_ref(v_str_1429_);
if v___x_1435_ == 0 {
crate::leanh::lean_dec_ref(v_str_1428_);
crate::leanh::lean_dec_ref(v_arg_1427_);
crate::leanh::lean_dec_ref(v_arg_1426_);
crate::leanh::lean_dec_ref(v_arg_1425_);
crate::leanh::lean_dec_ref(v_arg_1424_);
crate::leanh::lean_dec_ref(v_arg_1423_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1436_ = crate::leanh::lean_box(0);
return v___x_1436_;
} else {
v___x_1437_ = l_Lean_Expr_name_x3f___closed__10;
v___x_1438_ = lean_string_dec_eq(v_str_1428_, v___x_1437_);
crate::leanh::lean_dec_ref(v_str_1428_);
if v___x_1438_ == 0 {
crate::leanh::lean_dec_ref(v_arg_1427_);
crate::leanh::lean_dec_ref(v_arg_1426_);
crate::leanh::lean_dec_ref(v_arg_1425_);
crate::leanh::lean_dec_ref(v_arg_1424_);
crate::leanh::lean_dec_ref(v_arg_1423_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1439_ = crate::leanh::lean_box(0);
return v___x_1439_;
} else {
if crate::leanh::lean_obj_tag(v_arg_1427_) == 9 {
v_a_1440_ = crate::leanh::lean_ctor_get(v_arg_1427_, 0);
crate::leanh::lean_inc_ref(v_a_1440_);
crate::leanh::lean_dec_ref_known(v_arg_1427_, 1);
if crate::leanh::lean_obj_tag(v_a_1440_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1426_) == 9 {
v_a_1441_ = crate::leanh::lean_ctor_get(v_arg_1426_, 0);
crate::leanh::lean_inc_ref(v_a_1441_);
crate::leanh::lean_dec_ref_known(v_arg_1426_, 1);
if crate::leanh::lean_obj_tag(v_a_1441_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1425_) == 9 {
v_a_1442_ = crate::leanh::lean_ctor_get(v_arg_1425_, 0);
crate::leanh::lean_inc_ref(v_a_1442_);
crate::leanh::lean_dec_ref_known(v_arg_1425_, 1);
if crate::leanh::lean_obj_tag(v_a_1442_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1424_) == 9 {
v_a_1443_ = crate::leanh::lean_ctor_get(v_arg_1424_, 0);
crate::leanh::lean_inc_ref(v_a_1443_);
crate::leanh::lean_dec_ref_known(v_arg_1424_, 1);
if crate::leanh::lean_obj_tag(v_a_1443_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1423_) == 9 {
v_a_1444_ = crate::leanh::lean_ctor_get(v_arg_1423_, 0);
crate::leanh::lean_inc_ref(v_a_1444_);
crate::leanh::lean_dec_ref_known(v_arg_1423_, 1);
if crate::leanh::lean_obj_tag(v_a_1444_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1149_) == 9 {
v_a_1445_ = crate::leanh::lean_ctor_get(v_arg_1149_, 0);
crate::leanh::lean_inc_ref(v_a_1445_);
crate::leanh::lean_dec_ref_known(v_arg_1149_, 1);
if crate::leanh::lean_obj_tag(v_a_1445_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1147_) == 9 {
v_a_1446_ = crate::leanh::lean_ctor_get(v_arg_1147_, 0);
crate::leanh::lean_inc_ref(v_a_1446_);
crate::leanh::lean_dec_ref_known(v_arg_1147_, 1);
if crate::leanh::lean_obj_tag(v_a_1446_) == 1 {
v_val_1447_ = crate::leanh::lean_ctor_get(v_a_1440_, 0);
crate::leanh::lean_inc_ref(v_val_1447_);
crate::leanh::lean_dec_ref_known(v_a_1440_, 1);
v_val_1448_ = crate::leanh::lean_ctor_get(v_a_1441_, 0);
crate::leanh::lean_inc_ref(v_val_1448_);
crate::leanh::lean_dec_ref_known(v_a_1441_, 1);
v_val_1449_ = crate::leanh::lean_ctor_get(v_a_1442_, 0);
crate::leanh::lean_inc_ref(v_val_1449_);
crate::leanh::lean_dec_ref_known(v_a_1442_, 1);
v_val_1450_ = crate::leanh::lean_ctor_get(v_a_1443_, 0);
crate::leanh::lean_inc_ref(v_val_1450_);
crate::leanh::lean_dec_ref_known(v_a_1443_, 1);
v_val_1451_ = crate::leanh::lean_ctor_get(v_a_1444_, 0);
crate::leanh::lean_inc_ref(v_val_1451_);
crate::leanh::lean_dec_ref_known(v_a_1444_, 1);
v_val_1452_ = crate::leanh::lean_ctor_get(v_a_1445_, 0);
crate::leanh::lean_inc_ref(v_val_1452_);
crate::leanh::lean_dec_ref_known(v_a_1445_, 1);
v_val_1453_ = crate::leanh::lean_ctor_get(v_a_1446_, 0);
v_isSharedCheck_1461_ = (!crate::leanh::lean_is_exclusive(v_a_1446_)) as u8;
if v_isSharedCheck_1461_ == 0 {
v___x_1455_ = v_a_1446_;
v_isShared_1456_ = v_isSharedCheck_1461_;
state = 16; continue;
} else {
crate::leanh::lean_inc(v_val_1453_);
crate::leanh::lean_dec(v_a_1446_);
v___x_1455_ = crate::leanh::lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1461_;
state = 16; continue;
}
} else {
crate::leanh::lean_dec_ref(v_a_1446_);
crate::leanh::lean_dec_ref_known(v_a_1445_, 1);
crate::leanh::lean_dec_ref_known(v_a_1444_, 1);
crate::leanh::lean_dec_ref_known(v_a_1443_, 1);
crate::leanh::lean_dec_ref_known(v_a_1442_, 1);
crate::leanh::lean_dec_ref_known(v_a_1441_, 1);
crate::leanh::lean_dec_ref_known(v_a_1440_, 1);
v___x_1462_ = crate::leanh::lean_box(0);
return v___x_1462_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1445_, 1);
crate::leanh::lean_dec_ref_known(v_a_1444_, 1);
crate::leanh::lean_dec_ref_known(v_a_1443_, 1);
crate::leanh::lean_dec_ref_known(v_a_1442_, 1);
crate::leanh::lean_dec_ref_known(v_a_1441_, 1);
crate::leanh::lean_dec_ref_known(v_a_1440_, 1);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1463_ = crate::leanh::lean_box(0);
return v___x_1463_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1445_);
crate::leanh::lean_dec_ref_known(v_a_1444_, 1);
crate::leanh::lean_dec_ref_known(v_a_1443_, 1);
crate::leanh::lean_dec_ref_known(v_a_1442_, 1);
crate::leanh::lean_dec_ref_known(v_a_1441_, 1);
crate::leanh::lean_dec_ref_known(v_a_1440_, 1);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1464_ = crate::leanh::lean_box(0);
return v___x_1464_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1444_, 1);
crate::leanh::lean_dec_ref_known(v_a_1443_, 1);
crate::leanh::lean_dec_ref_known(v_a_1442_, 1);
crate::leanh::lean_dec_ref_known(v_a_1441_, 1);
crate::leanh::lean_dec_ref_known(v_a_1440_, 1);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1465_ = crate::leanh::lean_box(0);
return v___x_1465_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1444_);
crate::leanh::lean_dec_ref_known(v_a_1443_, 1);
crate::leanh::lean_dec_ref_known(v_a_1442_, 1);
crate::leanh::lean_dec_ref_known(v_a_1441_, 1);
crate::leanh::lean_dec_ref_known(v_a_1440_, 1);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1466_ = crate::leanh::lean_box(0);
return v___x_1466_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1443_, 1);
crate::leanh::lean_dec_ref_known(v_a_1442_, 1);
crate::leanh::lean_dec_ref_known(v_a_1441_, 1);
crate::leanh::lean_dec_ref_known(v_a_1440_, 1);
crate::leanh::lean_dec_ref(v_arg_1423_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1467_ = crate::leanh::lean_box(0);
return v___x_1467_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1443_);
crate::leanh::lean_dec_ref_known(v_a_1442_, 1);
crate::leanh::lean_dec_ref_known(v_a_1441_, 1);
crate::leanh::lean_dec_ref_known(v_a_1440_, 1);
crate::leanh::lean_dec_ref(v_arg_1423_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1468_ = crate::leanh::lean_box(0);
return v___x_1468_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1442_, 1);
crate::leanh::lean_dec_ref_known(v_a_1441_, 1);
crate::leanh::lean_dec_ref_known(v_a_1440_, 1);
crate::leanh::lean_dec_ref(v_arg_1424_);
crate::leanh::lean_dec_ref(v_arg_1423_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1469_ = crate::leanh::lean_box(0);
return v___x_1469_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1442_);
crate::leanh::lean_dec_ref_known(v_a_1441_, 1);
crate::leanh::lean_dec_ref_known(v_a_1440_, 1);
crate::leanh::lean_dec_ref(v_arg_1424_);
crate::leanh::lean_dec_ref(v_arg_1423_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1470_ = crate::leanh::lean_box(0);
return v___x_1470_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1441_, 1);
crate::leanh::lean_dec_ref_known(v_a_1440_, 1);
crate::leanh::lean_dec_ref(v_arg_1425_);
crate::leanh::lean_dec_ref(v_arg_1424_);
crate::leanh::lean_dec_ref(v_arg_1423_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1471_ = crate::leanh::lean_box(0);
return v___x_1471_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1441_);
crate::leanh::lean_dec_ref_known(v_a_1440_, 1);
crate::leanh::lean_dec_ref(v_arg_1425_);
crate::leanh::lean_dec_ref(v_arg_1424_);
crate::leanh::lean_dec_ref(v_arg_1423_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1472_ = crate::leanh::lean_box(0);
return v___x_1472_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1440_, 1);
crate::leanh::lean_dec_ref(v_arg_1426_);
crate::leanh::lean_dec_ref(v_arg_1425_);
crate::leanh::lean_dec_ref(v_arg_1424_);
crate::leanh::lean_dec_ref(v_arg_1423_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1473_ = crate::leanh::lean_box(0);
return v___x_1473_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1440_);
crate::leanh::lean_dec_ref(v_arg_1426_);
crate::leanh::lean_dec_ref(v_arg_1425_);
crate::leanh::lean_dec_ref(v_arg_1424_);
crate::leanh::lean_dec_ref(v_arg_1423_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1474_ = crate::leanh::lean_box(0);
return v___x_1474_;
}
} else {
crate::leanh::lean_dec_ref(v_arg_1427_);
crate::leanh::lean_dec_ref(v_arg_1426_);
crate::leanh::lean_dec_ref(v_arg_1425_);
crate::leanh::lean_dec_ref(v_arg_1424_);
crate::leanh::lean_dec_ref(v_arg_1423_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1475_ = crate::leanh::lean_box(0);
return v___x_1475_;
}
}
}
}
} else {
crate::leanh::lean_dec_ref_known(v_pre_1421_, 2);
crate::leanh::lean_dec_ref_known(v_pre_1420_, 2);
crate::leanh::lean_dec_ref_known(v_declName_1419_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1361_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1309_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1476_ = crate::leanh::lean_box(0);
return v___x_1476_;
}
} else {
crate::leanh::lean_dec_ref_known(v_pre_1420_, 2);
crate::leanh::lean_dec(v_pre_1421_);
crate::leanh::lean_dec_ref_known(v_declName_1419_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1361_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1309_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1477_ = crate::leanh::lean_box(0);
return v___x_1477_;
}
} else {
crate::leanh::lean_dec(v_pre_1420_);
crate::leanh::lean_dec_ref_known(v_declName_1419_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1361_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1309_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1478_ = crate::leanh::lean_box(0);
return v___x_1478_;
}
} else {
crate::leanh::lean_dec(v_declName_1419_);
crate::leanh::lean_dec_ref_known(v_fn_1361_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1309_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1479_ = crate::leanh::lean_box(0);
return v___x_1479_;
}
}
5 => {
crate::leanh::lean_inc_ref(v_fn_1418_);
v_fn_1480_ = crate::leanh::lean_ctor_get(v_fn_1418_, 0);
if crate::leanh::lean_obj_tag(v_fn_1480_) == 4 {
v_declName_1481_ = crate::leanh::lean_ctor_get(v_fn_1480_, 0);
crate::leanh::lean_inc(v_declName_1481_);
if crate::leanh::lean_obj_tag(v_declName_1481_) == 1 {
v_pre_1482_ = crate::leanh::lean_ctor_get(v_declName_1481_, 0);
crate::leanh::lean_inc(v_pre_1482_);
if crate::leanh::lean_obj_tag(v_pre_1482_) == 1 {
v_pre_1483_ = crate::leanh::lean_ctor_get(v_pre_1482_, 0);
crate::leanh::lean_inc(v_pre_1483_);
if crate::leanh::lean_obj_tag(v_pre_1483_) == 1 {
v_pre_1484_ = crate::leanh::lean_ctor_get(v_pre_1483_, 0);
if crate::leanh::lean_obj_tag(v_pre_1484_) == 0 {
v_arg_1485_ = crate::leanh::lean_ctor_get(v_fn_1148_, 1);
crate::leanh::lean_inc_ref(v_arg_1485_);
crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
v_arg_1486_ = crate::leanh::lean_ctor_get(v_fn_1220_, 1);
crate::leanh::lean_inc_ref(v_arg_1486_);
crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
v_arg_1487_ = crate::leanh::lean_ctor_get(v_fn_1262_, 1);
crate::leanh::lean_inc_ref(v_arg_1487_);
crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
v_arg_1488_ = crate::leanh::lean_ctor_get(v_fn_1309_, 1);
crate::leanh::lean_inc_ref(v_arg_1488_);
crate::leanh::lean_dec_ref_known(v_fn_1309_, 2);
v_arg_1489_ = crate::leanh::lean_ctor_get(v_fn_1361_, 1);
crate::leanh::lean_inc_ref(v_arg_1489_);
crate::leanh::lean_dec_ref_known(v_fn_1361_, 2);
v_arg_1490_ = crate::leanh::lean_ctor_get(v_fn_1418_, 1);
crate::leanh::lean_inc_ref(v_arg_1490_);
crate::leanh::lean_dec_ref_known(v_fn_1418_, 2);
v_str_1491_ = crate::leanh::lean_ctor_get(v_declName_1481_, 1);
crate::leanh::lean_inc_ref(v_str_1491_);
crate::leanh::lean_dec_ref_known(v_declName_1481_, 2);
v_str_1492_ = crate::leanh::lean_ctor_get(v_pre_1482_, 1);
crate::leanh::lean_inc_ref(v_str_1492_);
crate::leanh::lean_dec_ref_known(v_pre_1482_, 2);
v_str_1493_ = crate::leanh::lean_ctor_get(v_pre_1483_, 1);
crate::leanh::lean_inc_ref(v_str_1493_);
crate::leanh::lean_dec_ref_known(v_pre_1483_, 2);
v___x_1494_ = l_Lean_Expr_name_x3f___closed__0;
v___x_1495_ = lean_string_dec_eq(v_str_1493_, v___x_1494_);
crate::leanh::lean_dec_ref(v_str_1493_);
if v___x_1495_ == 0 {
crate::leanh::lean_dec_ref(v_str_1492_);
crate::leanh::lean_dec_ref(v_str_1491_);
crate::leanh::lean_dec_ref(v_arg_1490_);
crate::leanh::lean_dec_ref(v_arg_1489_);
crate::leanh::lean_dec_ref(v_arg_1488_);
crate::leanh::lean_dec_ref(v_arg_1487_);
crate::leanh::lean_dec_ref(v_arg_1486_);
crate::leanh::lean_dec_ref(v_arg_1485_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1496_ = crate::leanh::lean_box(0);
return v___x_1496_;
} else {
v___x_1497_ = l_Lean_Expr_name_x3f___closed__1;
v___x_1498_ = lean_string_dec_eq(v_str_1492_, v___x_1497_);
crate::leanh::lean_dec_ref(v_str_1492_);
if v___x_1498_ == 0 {
crate::leanh::lean_dec_ref(v_str_1491_);
crate::leanh::lean_dec_ref(v_arg_1490_);
crate::leanh::lean_dec_ref(v_arg_1489_);
crate::leanh::lean_dec_ref(v_arg_1488_);
crate::leanh::lean_dec_ref(v_arg_1487_);
crate::leanh::lean_dec_ref(v_arg_1486_);
crate::leanh::lean_dec_ref(v_arg_1485_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1499_ = crate::leanh::lean_box(0);
return v___x_1499_;
} else {
v___x_1500_ = l_Lean_Expr_name_x3f___closed__11;
v___x_1501_ = lean_string_dec_eq(v_str_1491_, v___x_1500_);
crate::leanh::lean_dec_ref(v_str_1491_);
if v___x_1501_ == 0 {
crate::leanh::lean_dec_ref(v_arg_1490_);
crate::leanh::lean_dec_ref(v_arg_1489_);
crate::leanh::lean_dec_ref(v_arg_1488_);
crate::leanh::lean_dec_ref(v_arg_1487_);
crate::leanh::lean_dec_ref(v_arg_1486_);
crate::leanh::lean_dec_ref(v_arg_1485_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1502_ = crate::leanh::lean_box(0);
return v___x_1502_;
} else {
if crate::leanh::lean_obj_tag(v_arg_1490_) == 9 {
v_a_1503_ = crate::leanh::lean_ctor_get(v_arg_1490_, 0);
crate::leanh::lean_inc_ref(v_a_1503_);
crate::leanh::lean_dec_ref_known(v_arg_1490_, 1);
if crate::leanh::lean_obj_tag(v_a_1503_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1489_) == 9 {
v_a_1504_ = crate::leanh::lean_ctor_get(v_arg_1489_, 0);
crate::leanh::lean_inc_ref(v_a_1504_);
crate::leanh::lean_dec_ref_known(v_arg_1489_, 1);
if crate::leanh::lean_obj_tag(v_a_1504_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1488_) == 9 {
v_a_1505_ = crate::leanh::lean_ctor_get(v_arg_1488_, 0);
crate::leanh::lean_inc_ref(v_a_1505_);
crate::leanh::lean_dec_ref_known(v_arg_1488_, 1);
if crate::leanh::lean_obj_tag(v_a_1505_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1487_) == 9 {
v_a_1506_ = crate::leanh::lean_ctor_get(v_arg_1487_, 0);
crate::leanh::lean_inc_ref(v_a_1506_);
crate::leanh::lean_dec_ref_known(v_arg_1487_, 1);
if crate::leanh::lean_obj_tag(v_a_1506_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1486_) == 9 {
v_a_1507_ = crate::leanh::lean_ctor_get(v_arg_1486_, 0);
crate::leanh::lean_inc_ref(v_a_1507_);
crate::leanh::lean_dec_ref_known(v_arg_1486_, 1);
if crate::leanh::lean_obj_tag(v_a_1507_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1485_) == 9 {
v_a_1508_ = crate::leanh::lean_ctor_get(v_arg_1485_, 0);
crate::leanh::lean_inc_ref(v_a_1508_);
crate::leanh::lean_dec_ref_known(v_arg_1485_, 1);
if crate::leanh::lean_obj_tag(v_a_1508_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1149_) == 9 {
v_a_1509_ = crate::leanh::lean_ctor_get(v_arg_1149_, 0);
crate::leanh::lean_inc_ref(v_a_1509_);
crate::leanh::lean_dec_ref_known(v_arg_1149_, 1);
if crate::leanh::lean_obj_tag(v_a_1509_) == 1 {
if crate::leanh::lean_obj_tag(v_arg_1147_) == 9 {
v_a_1510_ = crate::leanh::lean_ctor_get(v_arg_1147_, 0);
crate::leanh::lean_inc_ref(v_a_1510_);
crate::leanh::lean_dec_ref_known(v_arg_1147_, 1);
if crate::leanh::lean_obj_tag(v_a_1510_) == 1 {
v_val_1511_ = crate::leanh::lean_ctor_get(v_a_1503_, 0);
crate::leanh::lean_inc_ref(v_val_1511_);
crate::leanh::lean_dec_ref_known(v_a_1503_, 1);
v_val_1512_ = crate::leanh::lean_ctor_get(v_a_1504_, 0);
crate::leanh::lean_inc_ref(v_val_1512_);
crate::leanh::lean_dec_ref_known(v_a_1504_, 1);
v_val_1513_ = crate::leanh::lean_ctor_get(v_a_1505_, 0);
crate::leanh::lean_inc_ref(v_val_1513_);
crate::leanh::lean_dec_ref_known(v_a_1505_, 1);
v_val_1514_ = crate::leanh::lean_ctor_get(v_a_1506_, 0);
crate::leanh::lean_inc_ref(v_val_1514_);
crate::leanh::lean_dec_ref_known(v_a_1506_, 1);
v_val_1515_ = crate::leanh::lean_ctor_get(v_a_1507_, 0);
crate::leanh::lean_inc_ref(v_val_1515_);
crate::leanh::lean_dec_ref_known(v_a_1507_, 1);
v_val_1516_ = crate::leanh::lean_ctor_get(v_a_1508_, 0);
crate::leanh::lean_inc_ref(v_val_1516_);
crate::leanh::lean_dec_ref_known(v_a_1508_, 1);
v_val_1517_ = crate::leanh::lean_ctor_get(v_a_1509_, 0);
crate::leanh::lean_inc_ref(v_val_1517_);
crate::leanh::lean_dec_ref_known(v_a_1509_, 1);
v_val_1518_ = crate::leanh::lean_ctor_get(v_a_1510_, 0);
v_isSharedCheck_1526_ = (!crate::leanh::lean_is_exclusive(v_a_1510_)) as u8;
if v_isSharedCheck_1526_ == 0 {
v___x_1520_ = v_a_1510_;
v_isShared_1521_ = v_isSharedCheck_1526_;
state = 18; continue;
} else {
crate::leanh::lean_inc(v_val_1518_);
crate::leanh::lean_dec(v_a_1510_);
v___x_1520_ = crate::leanh::lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1526_;
state = 18; continue;
}
} else {
crate::leanh::lean_dec_ref(v_a_1510_);
crate::leanh::lean_dec_ref_known(v_a_1509_, 1);
crate::leanh::lean_dec_ref_known(v_a_1508_, 1);
crate::leanh::lean_dec_ref_known(v_a_1507_, 1);
crate::leanh::lean_dec_ref_known(v_a_1506_, 1);
crate::leanh::lean_dec_ref_known(v_a_1505_, 1);
crate::leanh::lean_dec_ref_known(v_a_1504_, 1);
crate::leanh::lean_dec_ref_known(v_a_1503_, 1);
v___x_1527_ = crate::leanh::lean_box(0);
return v___x_1527_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1509_, 1);
crate::leanh::lean_dec_ref_known(v_a_1508_, 1);
crate::leanh::lean_dec_ref_known(v_a_1507_, 1);
crate::leanh::lean_dec_ref_known(v_a_1506_, 1);
crate::leanh::lean_dec_ref_known(v_a_1505_, 1);
crate::leanh::lean_dec_ref_known(v_a_1504_, 1);
crate::leanh::lean_dec_ref_known(v_a_1503_, 1);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1528_ = crate::leanh::lean_box(0);
return v___x_1528_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1509_);
crate::leanh::lean_dec_ref_known(v_a_1508_, 1);
crate::leanh::lean_dec_ref_known(v_a_1507_, 1);
crate::leanh::lean_dec_ref_known(v_a_1506_, 1);
crate::leanh::lean_dec_ref_known(v_a_1505_, 1);
crate::leanh::lean_dec_ref_known(v_a_1504_, 1);
crate::leanh::lean_dec_ref_known(v_a_1503_, 1);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1529_ = crate::leanh::lean_box(0);
return v___x_1529_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1508_, 1);
crate::leanh::lean_dec_ref_known(v_a_1507_, 1);
crate::leanh::lean_dec_ref_known(v_a_1506_, 1);
crate::leanh::lean_dec_ref_known(v_a_1505_, 1);
crate::leanh::lean_dec_ref_known(v_a_1504_, 1);
crate::leanh::lean_dec_ref_known(v_a_1503_, 1);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1530_ = crate::leanh::lean_box(0);
return v___x_1530_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1508_);
crate::leanh::lean_dec_ref_known(v_a_1507_, 1);
crate::leanh::lean_dec_ref_known(v_a_1506_, 1);
crate::leanh::lean_dec_ref_known(v_a_1505_, 1);
crate::leanh::lean_dec_ref_known(v_a_1504_, 1);
crate::leanh::lean_dec_ref_known(v_a_1503_, 1);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1531_ = crate::leanh::lean_box(0);
return v___x_1531_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1507_, 1);
crate::leanh::lean_dec_ref_known(v_a_1506_, 1);
crate::leanh::lean_dec_ref_known(v_a_1505_, 1);
crate::leanh::lean_dec_ref_known(v_a_1504_, 1);
crate::leanh::lean_dec_ref_known(v_a_1503_, 1);
crate::leanh::lean_dec_ref(v_arg_1485_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1532_ = crate::leanh::lean_box(0);
return v___x_1532_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1507_);
crate::leanh::lean_dec_ref_known(v_a_1506_, 1);
crate::leanh::lean_dec_ref_known(v_a_1505_, 1);
crate::leanh::lean_dec_ref_known(v_a_1504_, 1);
crate::leanh::lean_dec_ref_known(v_a_1503_, 1);
crate::leanh::lean_dec_ref(v_arg_1485_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1533_ = crate::leanh::lean_box(0);
return v___x_1533_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1506_, 1);
crate::leanh::lean_dec_ref_known(v_a_1505_, 1);
crate::leanh::lean_dec_ref_known(v_a_1504_, 1);
crate::leanh::lean_dec_ref_known(v_a_1503_, 1);
crate::leanh::lean_dec_ref(v_arg_1486_);
crate::leanh::lean_dec_ref(v_arg_1485_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1534_ = crate::leanh::lean_box(0);
return v___x_1534_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1506_);
crate::leanh::lean_dec_ref_known(v_a_1505_, 1);
crate::leanh::lean_dec_ref_known(v_a_1504_, 1);
crate::leanh::lean_dec_ref_known(v_a_1503_, 1);
crate::leanh::lean_dec_ref(v_arg_1486_);
crate::leanh::lean_dec_ref(v_arg_1485_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1535_ = crate::leanh::lean_box(0);
return v___x_1535_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1505_, 1);
crate::leanh::lean_dec_ref_known(v_a_1504_, 1);
crate::leanh::lean_dec_ref_known(v_a_1503_, 1);
crate::leanh::lean_dec_ref(v_arg_1487_);
crate::leanh::lean_dec_ref(v_arg_1486_);
crate::leanh::lean_dec_ref(v_arg_1485_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1536_ = crate::leanh::lean_box(0);
return v___x_1536_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1505_);
crate::leanh::lean_dec_ref_known(v_a_1504_, 1);
crate::leanh::lean_dec_ref_known(v_a_1503_, 1);
crate::leanh::lean_dec_ref(v_arg_1487_);
crate::leanh::lean_dec_ref(v_arg_1486_);
crate::leanh::lean_dec_ref(v_arg_1485_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1537_ = crate::leanh::lean_box(0);
return v___x_1537_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1504_, 1);
crate::leanh::lean_dec_ref_known(v_a_1503_, 1);
crate::leanh::lean_dec_ref(v_arg_1488_);
crate::leanh::lean_dec_ref(v_arg_1487_);
crate::leanh::lean_dec_ref(v_arg_1486_);
crate::leanh::lean_dec_ref(v_arg_1485_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1538_ = crate::leanh::lean_box(0);
return v___x_1538_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1504_);
crate::leanh::lean_dec_ref_known(v_a_1503_, 1);
crate::leanh::lean_dec_ref(v_arg_1488_);
crate::leanh::lean_dec_ref(v_arg_1487_);
crate::leanh::lean_dec_ref(v_arg_1486_);
crate::leanh::lean_dec_ref(v_arg_1485_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1539_ = crate::leanh::lean_box(0);
return v___x_1539_;
}
} else {
crate::leanh::lean_dec_ref_known(v_a_1503_, 1);
crate::leanh::lean_dec_ref(v_arg_1489_);
crate::leanh::lean_dec_ref(v_arg_1488_);
crate::leanh::lean_dec_ref(v_arg_1487_);
crate::leanh::lean_dec_ref(v_arg_1486_);
crate::leanh::lean_dec_ref(v_arg_1485_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1540_ = crate::leanh::lean_box(0);
return v___x_1540_;
}
} else {
crate::leanh::lean_dec_ref(v_a_1503_);
crate::leanh::lean_dec_ref(v_arg_1489_);
crate::leanh::lean_dec_ref(v_arg_1488_);
crate::leanh::lean_dec_ref(v_arg_1487_);
crate::leanh::lean_dec_ref(v_arg_1486_);
crate::leanh::lean_dec_ref(v_arg_1485_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1541_ = crate::leanh::lean_box(0);
return v___x_1541_;
}
} else {
crate::leanh::lean_dec_ref(v_arg_1490_);
crate::leanh::lean_dec_ref(v_arg_1489_);
crate::leanh::lean_dec_ref(v_arg_1488_);
crate::leanh::lean_dec_ref(v_arg_1487_);
crate::leanh::lean_dec_ref(v_arg_1486_);
crate::leanh::lean_dec_ref(v_arg_1485_);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1542_ = crate::leanh::lean_box(0);
return v___x_1542_;
}
}
}
}
} else {
crate::leanh::lean_dec_ref_known(v_pre_1483_, 2);
crate::leanh::lean_dec_ref_known(v_pre_1482_, 2);
crate::leanh::lean_dec_ref_known(v_declName_1481_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1418_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1361_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1309_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1543_ = crate::leanh::lean_box(0);
return v___x_1543_;
}
} else {
crate::leanh::lean_dec(v_pre_1483_);
crate::leanh::lean_dec_ref_known(v_pre_1482_, 2);
crate::leanh::lean_dec_ref_known(v_declName_1481_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1418_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1361_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1309_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1544_ = crate::leanh::lean_box(0);
return v___x_1544_;
}
} else {
crate::leanh::lean_dec(v_pre_1482_);
crate::leanh::lean_dec_ref_known(v_declName_1481_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1418_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1361_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1309_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1545_ = crate::leanh::lean_box(0);
return v___x_1545_;
}
} else {
crate::leanh::lean_dec(v_declName_1481_);
crate::leanh::lean_dec_ref_known(v_fn_1418_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1361_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1309_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1546_ = crate::leanh::lean_box(0);
return v___x_1546_;
}
} else {
crate::leanh::lean_dec_ref_known(v_fn_1418_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1361_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1309_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1547_ = crate::leanh::lean_box(0);
return v___x_1547_;
}
}
_ => {
crate::leanh::lean_dec_ref_known(v_fn_1361_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1309_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
crate::leanh::lean_dec_ref(v_arg_1149_);
crate::leanh::lean_dec_ref(v_arg_1147_);
v___x_1548_ = crate::leanh::lean_box(0);
return v___x_1548_;
}
}
                                                                    }
                                                                    _ => {
                                                                        crate::leanh::lean_dec_ref_known(v_fn_1309_, 2);
                                                                        crate::leanh::lean_dec_ref_known(v_fn_1262_, 2);
                                                                        crate::leanh::lean_dec_ref_known(v_fn_1220_, 2);
                                                                        crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1149_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_1147_,
                                                                        );
                                                                        v___x_1549_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        return v___x_1549_;
                                                                    }
                                                                }
                                                            }
                                                            _ => {
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_fn_1262_, 2,
                                                                );
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_fn_1220_, 2,
                                                                );
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_fn_1148_, 2,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_1149_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_1147_,
                                                                );
                                                                v___x_1550_ =
                                                                    crate::leanh::lean_box(0);
                                                                return v___x_1550_;
                                                            }
                                                        }
                                                    }
                                                    _ => {
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_fn_1220_, 2,
                                                        );
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_fn_1148_, 2,
                                                        );
                                                        crate::leanh::lean_dec_ref(v_arg_1149_);
                                                        crate::leanh::lean_dec_ref(v_arg_1147_);
                                                        v___x_1551_ = crate::leanh::lean_box(0);
                                                        return v___x_1551_;
                                                    }
                                                }
                                            }
                                            _ => {
                                                crate::leanh::lean_dec_ref_known(v_fn_1148_, 2);
                                                crate::leanh::lean_dec_ref(v_arg_1149_);
                                                crate::leanh::lean_dec_ref(v_arg_1147_);
                                                v___x_1552_ = crate::leanh::lean_box(0);
                                                return v___x_1552_;
                                            }
                                        }
                                    }
                                    _ => {
                                        crate::leanh::lean_dec_ref(v_arg_1149_);
                                        crate::leanh::lean_dec_ref(v_fn_1148_);
                                        crate::leanh::lean_dec_ref(v_arg_1147_);
                                        v___x_1553_ = crate::leanh::lean_box(0);
                                        return v___x_1553_;
                                    }
                                }
                            }
                            4 => {
                                v_declName_1554_ = crate::leanh::lean_ctor_get(v_fn_1146_, 0);
                                crate::leanh::lean_inc(v_declName_1554_);
                                if crate::leanh::lean_obj_tag(v_declName_1554_) == 1 {
                                    v_pre_1555_ = crate::leanh::lean_ctor_get(v_declName_1554_, 0);
                                    crate::leanh::lean_inc(v_pre_1555_);
                                    if crate::leanh::lean_obj_tag(v_pre_1555_) == 1 {
                                        v_pre_1556_ = crate::leanh::lean_ctor_get(v_pre_1555_, 0);
                                        crate::leanh::lean_inc(v_pre_1556_);
                                        if crate::leanh::lean_obj_tag(v_pre_1556_) == 1 {
                                            v_pre_1557_ =
                                                crate::leanh::lean_ctor_get(v_pre_1556_, 0);
                                            if crate::leanh::lean_obj_tag(v_pre_1557_) == 0 {
                                                v_arg_1558_ =
                                                    crate::leanh::lean_ctor_get(v_x_1124_, 1);
                                                crate::leanh::lean_inc_ref(v_arg_1558_);
                                                crate::leanh::lean_dec_ref_known(v_x_1124_, 2);
                                                v_str_1559_ = crate::leanh::lean_ctor_get(
                                                    v_declName_1554_,
                                                    1,
                                                );
                                                crate::leanh::lean_inc_ref(v_str_1559_);
                                                crate::leanh::lean_dec_ref_known(
                                                    v_declName_1554_,
                                                    2,
                                                );
                                                v_str_1560_ =
                                                    crate::leanh::lean_ctor_get(v_pre_1555_, 1);
                                                crate::leanh::lean_inc_ref(v_str_1560_);
                                                crate::leanh::lean_dec_ref_known(v_pre_1555_, 2);
                                                v_str_1561_ =
                                                    crate::leanh::lean_ctor_get(v_pre_1556_, 1);
                                                crate::leanh::lean_inc_ref(v_str_1561_);
                                                crate::leanh::lean_dec_ref_known(v_pre_1556_, 2);
                                                v___x_1562_ = l_Lean_Expr_name_x3f___closed__0;
                                                v___x_1563_ =
                                                    lean_string_dec_eq(v_str_1561_, v___x_1562_);
                                                crate::leanh::lean_dec_ref(v_str_1561_);
                                                if v___x_1563_ == 0 {
                                                    crate::leanh::lean_dec_ref(v_str_1560_);
                                                    crate::leanh::lean_dec_ref(v_str_1559_);
                                                    crate::leanh::lean_dec_ref(v_arg_1558_);
                                                    v___x_1564_ = crate::leanh::lean_box(0);
                                                    return v___x_1564_;
                                                } else {
                                                    v___x_1565_ = l_Lean_Expr_name_x3f___closed__1;
                                                    v___x_1566_ = lean_string_dec_eq(
                                                        v_str_1560_,
                                                        v___x_1565_,
                                                    );
                                                    crate::leanh::lean_dec_ref(v_str_1560_);
                                                    if v___x_1566_ == 0 {
                                                        crate::leanh::lean_dec_ref(v_str_1559_);
                                                        crate::leanh::lean_dec_ref(v_arg_1558_);
                                                        v___x_1567_ = crate::leanh::lean_box(0);
                                                        return v___x_1567_;
                                                    } else {
                                                        v___x_1568_ =
                                                            l_Lean_Expr_name_x3f___closed__12;
                                                        v___x_1569_ = lean_string_dec_eq(
                                                            v_str_1559_,
                                                            v___x_1568_,
                                                        );
                                                        crate::leanh::lean_dec_ref(v_str_1559_);
                                                        if v___x_1569_ == 0 {
                                                            crate::leanh::lean_dec_ref(v_arg_1558_);
                                                            v___x_1570_ = crate::leanh::lean_box(0);
                                                            return v___x_1570_;
                                                        } else {
                                                            if crate::leanh::lean_obj_tag(
                                                                v_arg_1558_,
                                                            ) == 9
                                                            {
                                                                v_a_1571_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_arg_1558_,
                                                                        0,
                                                                    );
                                                                crate::leanh::lean_inc_ref(
                                                                    v_a_1571_,
                                                                );
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_arg_1558_,
                                                                    1,
                                                                );
                                                                if crate::leanh::lean_obj_tag(
                                                                    v_a_1571_,
                                                                ) == 1
                                                                {
                                                                    v_val_1572_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v_a_1571_, 0,
                                                                        );
                                                                    v_isSharedCheck_1580_ = (!crate::leanh::lean_is_exclusive(v_a_1571_)) as u8;
                                                                    if v_isSharedCheck_1580_ == 0 {
                                                                        v___x_1574_ = v_a_1571_;
                                                                        v_isShared_1575_ =
                                                                            v_isSharedCheck_1580_;
                                                                        state = 20;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_val_1572_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_1571_,
                                                                        );
                                                                        v___x_1574_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_1575_ =
                                                                            v_isSharedCheck_1580_;
                                                                        state = 20;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_a_1571_,
                                                                    );
                                                                    v___x_1581_ =
                                                                        crate::leanh::lean_box(0);
                                                                    return v___x_1581_;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_1558_,
                                                                );
                                                                v___x_1582_ =
                                                                    crate::leanh::lean_box(0);
                                                                return v___x_1582_;
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref_known(v_pre_1556_, 2);
                                                crate::leanh::lean_dec_ref_known(v_pre_1555_, 2);
                                                crate::leanh::lean_dec_ref_known(
                                                    v_declName_1554_,
                                                    2,
                                                );
                                                crate::leanh::lean_dec_ref_known(v_x_1124_, 2);
                                                v___x_1583_ = crate::leanh::lean_box(0);
                                                return v___x_1583_;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref_known(v_pre_1555_, 2);
                                            crate::leanh::lean_dec(v_pre_1556_);
                                            crate::leanh::lean_dec_ref_known(v_declName_1554_, 2);
                                            crate::leanh::lean_dec_ref_known(v_x_1124_, 2);
                                            v___x_1584_ = crate::leanh::lean_box(0);
                                            return v___x_1584_;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_pre_1555_);
                                        crate::leanh::lean_dec_ref_known(v_declName_1554_, 2);
                                        crate::leanh::lean_dec_ref_known(v_x_1124_, 2);
                                        v___x_1585_ = crate::leanh::lean_box(0);
                                        return v___x_1585_;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_declName_1554_);
                                    crate::leanh::lean_dec_ref_known(v_x_1124_, 2);
                                    v___x_1586_ = crate::leanh::lean_box(0);
                                    return v___x_1586_;
                                }
                            }
                            _ => {
                                crate::leanh::lean_dec_ref_known(v_x_1124_, 2);
                                v___x_1587_ = crate::leanh::lean_box(0);
                                return v___x_1587_;
                            }
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec_ref(v_x_1124_);
                        v___x_1588_ = crate::leanh::lean_box(0);
                        return v___x_1588_;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_1151_) == 0 {
                    crate::leanh::lean_dec_ref(v_arg_1149_);
                    v___x_1152_ = crate::leanh::lean_box(0);
                    return v___x_1152_;
                } else {
                    v_val_1153_ = crate::leanh::lean_ctor_get(v___y_1151_, 0);
                    crate::leanh::lean_inc(v_val_1153_);
                    crate::leanh::lean_dec_ref_known(v___y_1151_, 1);
                    v___x_1154_ = l_Lean_Expr_name_x3f(v_arg_1149_);
                    if crate::leanh::lean_obj_tag(v___x_1154_) == 0 {
                        crate::leanh::lean_dec(v_val_1153_);
                        return v___x_1154_;
                    } else {
                        v_val_1155_ = crate::leanh::lean_ctor_get(v___x_1154_, 0);
                        v_isSharedCheck_1163_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1154_)) as u8;
                        if v_isSharedCheck_1163_ == 0 {
                            v___x_1157_ = v___x_1154_;
                            v_isShared_1158_ = v_isSharedCheck_1163_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1155_);
                            crate::leanh::lean_dec(v___x_1154_);
                            v___x_1157_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_1157_, 0, v___x_1159_);
                    v___x_1161_ = v___x_1157_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1162_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1159_);
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
                    crate::leanh::lean_ctor_set(v___x_1189_, 0, v___x_1191_);
                    v___x_1193_ = v___x_1189_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1194_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1191_);
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
                    crate::leanh::lean_ctor_set(v___x_1207_, 0, v___x_1209_);
                    v___x_1211_ = v___x_1207_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1212_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1209_);
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
                    crate::leanh::lean_ctor_set(v___x_1245_, 0, v___x_1247_);
                    v___x_1249_ = v___x_1245_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1250_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
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
                    crate::leanh::lean_ctor_set(v___x_1290_, 0, v___x_1292_);
                    v___x_1294_ = v___x_1290_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1295_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1292_);
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
                    crate::leanh::lean_ctor_set(v___x_1340_, 0, v___x_1342_);
                    v___x_1344_ = v___x_1340_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1345_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
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
                    crate::leanh::lean_ctor_set(v___x_1395_, 0, v___x_1397_);
                    v___x_1399_ = v___x_1395_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1400_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
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
                    crate::leanh::lean_ctor_set(v___x_1455_, 0, v___x_1457_);
                    v___x_1459_ = v___x_1455_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1460_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1457_);
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
                    crate::leanh::lean_ctor_set(v___x_1520_, 0, v___x_1522_);
                    v___x_1524_ = v___x_1520_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1525_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1522_);
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
                    crate::leanh::lean_ctor_set(v___x_1574_, 0, v___x_1576_);
                    v___x_1578_ = v___x_1574_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1579_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
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
pub unsafe fn runtime_initialize_Lean_Util_Recognizers(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Environment(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_Recognizers(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_Recognizers(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Environment(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Recognizers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_Recognizers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_Recognizers(builtin);
}
