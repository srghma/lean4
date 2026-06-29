// Lean compiler output
// Module: Lean.Meta.Order
// Imports: Lean.Meta.PProdN Lean.Meta.AppBuilder Init.Internal.Order.Basic
use crate::r#gen::Init::Data::Array::Basic::l_Array_reverse___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Internal::Order::Basic::{
    initialize_Init_Internal_Order_Basic, runtime_initialize_Init_Internal_Order_Basic,
};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_isAppOf, l_Lean_instInhabitedExpr};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofList, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkAppOptM, runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_mkLambdaFVars;
use crate::r#gen::Lean::Meta::PProdN::{
    initialize_Lean_Meta_PProdN, l_Lean_Meta_PProdN_genMk___redArg,
    runtime_initialize_Lean_Meta_PProdN,
};
use crate::ffi::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::ffi::lean_st_ref_get;
use crate::ffi::lean_infer_type;
pub static l_Lean_Meta_mkInstPiOfInstForall___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkInstPiOfInstForall___closed__1_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [79, 114, 100, 101, 114, 0],
    };
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkInstPiOfInstForall___closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [67, 67, 80, 79, 0],
    };
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_mkInstPiOfInstForall___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_mkInstPiOfInstForall___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__1_value)
                as *mut crate::leanh::LeanObject,
            489434913524309295 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_mkInstPiOfInstForall___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__2_value)
                as *mut crate::leanh::LeanObject,
            14719117893866890003 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkInstPiOfInstForall___closed__4_value: crate::leanh::LeanStringObject<16> =
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
            67, 111, 109, 112, 108, 101, 116, 101, 76, 97, 116, 116, 105, 99, 101, 0,
        ],
    };
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_mkInstPiOfInstForall___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_mkInstPiOfInstForall___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__5_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__1_value)
                as *mut crate::leanh::LeanObject,
            489434913524309295 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_mkInstPiOfInstForall___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__5_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__4_value)
                as *mut crate::leanh::LeanObject,
            7757046375493111023 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkInstPiOfInstForall___closed__6_value: crate::leanh::LeanStringObject<42> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 42,
        m_capacity: 42,
        m_length: 41,
        m_data: [
            109, 107, 73, 110, 115, 116, 80, 105, 79, 102, 73, 110, 115, 116, 70, 111, 114, 97,
            108, 108, 58, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 121, 112,
            101, 32, 111, 102, 32, 0,
        ],
    };
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkInstPiOfInstForall___closed__8_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            105, 110, 115, 116, 67, 111, 109, 112, 108, 101, 116, 101, 76, 97, 116, 116, 105, 99,
            101, 80, 105, 0,
        ],
    };
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_mkInstPiOfInstForall___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_mkInstPiOfInstForall___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__9_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__1_value)
                as *mut crate::leanh::LeanObject,
            489434913524309295 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_mkInstPiOfInstForall___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__9_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__8_value)
                as *mut crate::leanh::LeanObject,
            2333849305392694232 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkInstPiOfInstForall___closed__10_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [105, 110, 115, 116, 67, 67, 80, 79, 80, 105, 0],
    };
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_mkInstPiOfInstForall___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_mkInstPiOfInstForall___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__11_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__1_value)
                as *mut crate::leanh::LeanObject,
            489434913524309295 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_mkInstPiOfInstForall___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__11_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__10_value)
                as *mut crate::leanh::LeanObject,
            16137463000135501002 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkFixOfMonFun___closed__0_value: crate::leanh::LeanStringObject<35> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 35,
        m_capacity: 35,
        m_length: 34,
        m_data: [
            109, 107, 70, 105, 120, 79, 102, 77, 111, 110, 70, 117, 110, 58, 32, 117, 110, 101,
            120, 112, 101, 99, 116, 101, 100, 32, 116, 121, 112, 101, 32, 111, 102, 32, 0,
        ],
    };
static mut l_Lean_Meta_mkFixOfMonFun___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkFixOfMonFun___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_mkFixOfMonFun___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkFixOfMonFun___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkFixOfMonFun___closed__2_value: crate::leanh::LeanStringObject<13> =
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
        m_data: [108, 102, 112, 95, 109, 111, 110, 111, 116, 111, 110, 101, 0],
    };
static mut l_Lean_Meta_mkFixOfMonFun___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkFixOfMonFun___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_mkFixOfMonFun___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_mkFixOfMonFun___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkFixOfMonFun___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__1_value)
                as *mut crate::leanh::LeanObject,
            489434913524309295 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_mkFixOfMonFun___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkFixOfMonFun___closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkFixOfMonFun___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2249643242235982818 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkFixOfMonFun___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkFixOfMonFun___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkFixOfMonFun___closed__4_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [102, 105, 120, 0],
    };
static mut l_Lean_Meta_mkFixOfMonFun___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkFixOfMonFun___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_mkFixOfMonFun___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_mkFixOfMonFun___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkFixOfMonFun___closed__5_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__1_value)
                as *mut crate::leanh::LeanObject,
            489434913524309295 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_mkFixOfMonFun___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkFixOfMonFun___closed__5_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkFixOfMonFun___closed__4_value)
                as *mut crate::leanh::LeanObject,
            1180902349914728466 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkFixOfMonFun___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkFixOfMonFun___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_toPartialOrder___closed__0_value: crate::leanh::LeanStringObject<40> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            103, 101, 116, 85, 110, 100, 101, 114, 108, 121, 105, 110, 103, 79, 114, 100, 101, 114,
            58, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 121, 112, 101, 32,
            111, 102, 32, 0,
        ],
    };
static mut l_Lean_Meta_toPartialOrder___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_toPartialOrder___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_toPartialOrder___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_toPartialOrder___closed__2_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
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
            116, 111, 80, 97, 114, 116, 105, 97, 108, 79, 114, 100, 101, 114, 0,
        ],
    };
static mut l_Lean_Meta_toPartialOrder___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_toPartialOrder___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_toPartialOrder___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__1_value)
                as *mut crate::leanh::LeanObject,
            489434913524309295 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_toPartialOrder___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__4_value)
                as *mut crate::leanh::LeanObject,
            7757046375493111023 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_toPartialOrder___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__3_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__2_value)
                as *mut crate::leanh::LeanObject,
            17628181181762307085 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_toPartialOrder___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_toPartialOrder___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_toPartialOrder___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__1_value)
                as *mut crate::leanh::LeanObject,
            489434913524309295 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_toPartialOrder___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__2_value)
                as *mut crate::leanh::LeanObject,
            14719117893866890003 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_toPartialOrder___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__2_value)
                as *mut crate::leanh::LeanObject,
            3289060660584192201 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_toPartialOrder___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkInstCCPOPProd___closed__0_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [105, 110, 115, 116, 67, 67, 80, 79, 80, 80, 114, 111, 100, 0],
    };
static mut l_Lean_Meta_mkInstCCPOPProd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstCCPOPProd___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_mkInstCCPOPProd___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_mkInstCCPOPProd___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstCCPOPProd___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__1_value)
                as *mut crate::leanh::LeanObject,
            489434913524309295 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_mkInstCCPOPProd___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstCCPOPProd___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstCCPOPProd___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17323779659096317889 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkInstCCPOPProd___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstCCPOPProd___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_mkInstCCPOPProd___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkInstCCPOPProd___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkInstCCPOPProd___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkInstCCPOPProd___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkInstCompleteLatticePProd___closed__0_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        105, 110, 115, 116, 67, 111, 109, 112, 108, 101, 116, 101, 76, 97, 116, 116, 105, 99, 101,
        80, 80, 114, 111, 100, 0,
    ],
};
static mut l_Lean_Meta_mkInstCompleteLatticePProd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstCompleteLatticePProd___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_mkInstCompleteLatticePProd___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_mkInstCompleteLatticePProd___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_mkInstCompleteLatticePProd___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__1_value)
            as *mut crate::leanh::LeanObject,
        489434913524309295 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_mkInstCompleteLatticePProd___closed__1_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkInstCompleteLatticePProd___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkInstCompleteLatticePProd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14055657004040094196 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_mkInstCompleteLatticePProd___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstCompleteLatticePProd___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkPackedPPRodInstance___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_mkInstCompleteLatticePProd___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_mkPackedPPRodInstance___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkPackedPPRodInstance___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkPackedPPRodInstance___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_mkInstCCPOPProd___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_mkPackedPPRodInstance___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkPackedPPRodInstance___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkPackedPPRodInstance___closed__2_value: crate::leanh::LeanStringObject<42> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 42,
        m_capacity: 42,
        m_length: 41,
        m_data: [
            109, 107, 80, 97, 99, 107, 101, 100, 80, 80, 82, 111, 111, 100, 73, 110, 115, 116, 97,
            110, 99, 101, 58, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 121,
            112, 101, 115, 32, 0,
        ],
    };
static mut l_Lean_Meta_mkPackedPPRodInstance___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkPackedPPRodInstance___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_mkPackedPPRodInstance___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkPackedPPRodInstance___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkPackedPPRodInstance___closed__4_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [32, 111, 102, 32, 0],
    };
static mut l_Lean_Meta_mkPackedPPRodInstance___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkPackedPPRodInstance___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_mkPackedPPRodInstance___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkPackedPPRodInstance___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0_spec__0(
    mut v_msgData_586_: *mut crate::leanh::LeanObject,
    mut v___y_587_: *mut crate::leanh::LeanObject,
    mut v___y_588_: *mut crate::leanh::LeanObject,
    mut v___y_589_: *mut crate::leanh::LeanObject,
    mut v___y_590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_592_ = lean_st_ref_get(v___y_590_);
    v_env_593_ = crate::leanh::lean_ctor_get(v___x_592_, 0);
    crate::leanh::lean_inc_ref(v_env_593_);
    crate::leanh::lean_dec(v___x_592_);
    v___x_594_ = lean_st_ref_get(v___y_588_);
    v_mctx_595_ = crate::leanh::lean_ctor_get(v___x_594_, 0);
    crate::leanh::lean_inc_ref(v_mctx_595_);
    crate::leanh::lean_dec(v___x_594_);
    v_lctx_596_ = crate::leanh::lean_ctor_get(v___y_587_, 2);
    v_options_597_ = crate::leanh::lean_ctor_get(v___y_589_, 2);
    crate::leanh::lean_inc_ref(v_options_597_);
    crate::leanh::lean_inc_ref(v_lctx_596_);
    v___x_598_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_598_, 0, v_env_593_);
    crate::leanh::lean_ctor_set(v___x_598_, 1, v_mctx_595_);
    crate::leanh::lean_ctor_set(v___x_598_, 2, v_lctx_596_);
    crate::leanh::lean_ctor_set(v___x_598_, 3, v_options_597_);
    v___x_599_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_599_, 0, v___x_598_);
    crate::leanh::lean_ctor_set(v___x_599_, 1, v_msgData_586_);
    v___x_600_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_600_, 0, v___x_599_);
    return v___x_600_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0_spec__0___boxed(
    mut v_msgData_601_: *mut crate::leanh::LeanObject,
    mut v___y_602_: *mut crate::leanh::LeanObject,
    mut v___y_603_: *mut crate::leanh::LeanObject,
    mut v___y_604_: *mut crate::leanh::LeanObject,
    mut v___y_605_: *mut crate::leanh::LeanObject,
    mut v___y_606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_607_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0_spec__0(v_msgData_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
    crate::leanh::lean_dec(v___y_605_);
    crate::leanh::lean_dec_ref(v___y_604_);
    crate::leanh::lean_dec(v___y_603_);
    crate::leanh::lean_dec_ref(v___y_602_);
    return v_res_607_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(
    mut v_msg_608_: *mut crate::leanh::LeanObject,
    mut v___y_609_: *mut crate::leanh::LeanObject,
    mut v___y_610_: *mut crate::leanh::LeanObject,
    mut v___y_611_: *mut crate::leanh::LeanObject,
    mut v___y_612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_619_: u8 = 0;
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_624_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_614_ = crate::leanh::lean_ctor_get(v___y_611_, 5);
                v___x_615_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0_spec__0(v_msg_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
                v_a_616_ = crate::leanh::lean_ctor_get(v___x_615_, 0);
                v_isSharedCheck_624_ = (!crate::leanh::lean_is_exclusive(v___x_615_)) as u8;
                if v_isSharedCheck_624_ == 0 {
                    v___x_618_ = v___x_615_;
                    v_isShared_619_ = v_isSharedCheck_624_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_616_);
                    crate::leanh::lean_dec(v___x_615_);
                    v___x_618_ = crate::leanh::lean_box(0);
                    v_isShared_619_ = v_isSharedCheck_624_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_614_);
                v___x_620_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_620_, 0, v_ref_614_);
                crate::leanh::lean_ctor_set(v___x_620_, 1, v_a_616_);
                if v_isShared_619_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_618_, 1);
                    crate::leanh::lean_ctor_set(v___x_618_, 0, v___x_620_);
                    v___x_622_ = v___x_618_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_623_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
                    v___x_622_ = v_reuseFailAlloc_623_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_622_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg___boxed(
    mut v_msg_625_: *mut crate::leanh::LeanObject,
    mut v___y_626_: *mut crate::leanh::LeanObject,
    mut v___y_627_: *mut crate::leanh::LeanObject,
    mut v___y_628_: *mut crate::leanh::LeanObject,
    mut v___y_629_: *mut crate::leanh::LeanObject,
    mut v___y_630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_631_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(
        v_msg_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_,
    );
    crate::leanh::lean_dec(v___y_629_);
    crate::leanh::lean_dec_ref(v___y_628_);
    crate::leanh::lean_dec(v___y_627_);
    crate::leanh::lean_dec_ref(v___y_626_);
    return v_res_631_;
}
pub unsafe fn _init_l_Lean_Meta_mkInstPiOfInstForall___closed__7() -> *mut crate::leanh::LeanObject
{
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_645_ = l_Lean_Meta_mkInstPiOfInstForall___closed__6;
    v___x_646_ = l_Lean_stringToMessageData(v___x_645_);
    return v___x_646_;
}
pub unsafe fn l_Lean_Meta_mkInstPiOfInstForall(
    mut v_x_657_: *mut crate::leanh::LeanObject,
    mut v_inst_658_: *mut crate::leanh::LeanObject,
    mut v_a_659_: *mut crate::leanh::LeanObject,
    mut v_a_660_: *mut crate::leanh::LeanObject,
    mut v_a_661_: *mut crate::leanh::LeanObject,
    mut v_a_662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: u8 = 0;
    let mut v___x_668_: u8 = 0;
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: u8 = 0;
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_681_: u8 = 0;
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: u8 = 0;
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_690_: u8 = 0;
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_705_: u8 = 0;
    let mut v_isSharedCheck_706_: u8 = 0;
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_711_: u8 = 0;
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: u8 = 0;
    let mut v___x_716_: u8 = 0;
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_721_: u8 = 0;
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_736_: u8 = 0;
    let mut v_isSharedCheck_737_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_662_);
                crate::leanh::lean_inc_ref(v_a_661_);
                crate::leanh::lean_inc(v_a_660_);
                crate::leanh::lean_inc_ref(v_a_659_);
                crate::leanh::lean_inc_ref(v_inst_658_);
                v___x_664_ = lean_infer_type(v_inst_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
                if crate::leanh::lean_obj_tag(v___x_664_) == 0 {
                    v_a_665_ = crate::leanh::lean_ctor_get(v___x_664_, 0);
                    crate::leanh::lean_inc(v_a_665_);
                    crate::leanh::lean_dec_ref_known(v___x_664_, 1);
                    v___x_666_ = l_Lean_Meta_mkInstPiOfInstForall___closed__3;
                    v___x_667_ = l_Lean_Expr_isAppOf(v_a_665_, v___x_666_);
                    crate::leanh::lean_dec(v_a_665_);
                    v___x_668_ = 1;
                    if v___x_667_ == 0 {
                        crate::leanh::lean_inc(v_a_662_);
                        crate::leanh::lean_inc_ref(v_a_661_);
                        crate::leanh::lean_inc(v_a_660_);
                        crate::leanh::lean_inc_ref(v_a_659_);
                        crate::leanh::lean_inc_ref(v_inst_658_);
                        v___x_669_ =
                            lean_infer_type(v_inst_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
                        if crate::leanh::lean_obj_tag(v___x_669_) == 0 {
                            v_a_670_ = crate::leanh::lean_ctor_get(v___x_669_, 0);
                            crate::leanh::lean_inc(v_a_670_);
                            crate::leanh::lean_dec_ref_known(v___x_669_, 1);
                            v___x_671_ = l_Lean_Meta_mkInstPiOfInstForall___closed__5;
                            v___x_672_ = l_Lean_Expr_isAppOf(v_a_670_, v___x_671_);
                            crate::leanh::lean_dec(v_a_670_);
                            if v___x_672_ == 0 {
                                crate::leanh::lean_dec_ref(v_x_657_);
                                v___x_673_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_mkInstPiOfInstForall___closed__7
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_mkInstPiOfInstForall___closed__7_once
                                    ),
                                    _init_l_Lean_Meta_mkInstPiOfInstForall___closed__7,
                                );
                                v___x_674_ = l_Lean_MessageData_ofExpr(v_inst_658_);
                                v___x_675_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_675_, 0, v___x_673_);
                                crate::leanh::lean_ctor_set(v___x_675_, 1, v___x_674_);
                                v___x_676_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(v___x_675_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
                                return v___x_676_;
                            } else {
                                crate::leanh::lean_inc(v_a_662_);
                                crate::leanh::lean_inc_ref(v_a_661_);
                                crate::leanh::lean_inc(v_a_660_);
                                crate::leanh::lean_inc_ref(v_a_659_);
                                crate::leanh::lean_inc_ref(v_x_657_);
                                v___x_677_ = lean_infer_type(
                                    v_x_657_, v_a_659_, v_a_660_, v_a_661_, v_a_662_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_677_) == 0 {
                                    v_a_678_ = crate::leanh::lean_ctor_get(v___x_677_, 0);
                                    v_isSharedCheck_706_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_677_)) as u8;
                                    if v_isSharedCheck_706_ == 0 {
                                        v___x_680_ = v___x_677_;
                                        v_isShared_681_ = v_isSharedCheck_706_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_678_);
                                        crate::leanh::lean_dec(v___x_677_);
                                        v___x_680_ = crate::leanh::lean_box(0);
                                        v_isShared_681_ = v_isSharedCheck_706_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_inst_658_);
                                    crate::leanh::lean_dec_ref(v_x_657_);
                                    return v___x_677_;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_inst_658_);
                            crate::leanh::lean_dec_ref(v_x_657_);
                            return v___x_669_;
                        }
                    } else {
                        crate::leanh::lean_inc(v_a_662_);
                        crate::leanh::lean_inc_ref(v_a_661_);
                        crate::leanh::lean_inc(v_a_660_);
                        crate::leanh::lean_inc_ref(v_a_659_);
                        crate::leanh::lean_inc_ref(v_x_657_);
                        v___x_707_ =
                            lean_infer_type(v_x_657_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
                        if crate::leanh::lean_obj_tag(v___x_707_) == 0 {
                            v_a_708_ = crate::leanh::lean_ctor_get(v___x_707_, 0);
                            v_isSharedCheck_737_ =
                                (!crate::leanh::lean_is_exclusive(v___x_707_)) as u8;
                            if v_isSharedCheck_737_ == 0 {
                                v___x_710_ = v___x_707_;
                                v_isShared_711_ = v_isSharedCheck_737_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_708_);
                                crate::leanh::lean_dec(v___x_707_);
                                v___x_710_ = crate::leanh::lean_box(0);
                                v_isShared_711_ = v_isSharedCheck_737_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_inst_658_);
                            crate::leanh::lean_dec_ref(v_x_657_);
                            return v___x_707_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_658_);
                    crate::leanh::lean_dec_ref(v_x_657_);
                    return v___x_664_;
                }
            }
            1 => {
                v___x_682_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_683_ = lean_mk_empty_array_with_capacity(v___x_682_);
                v___x_684_ = lean_array_push(v___x_683_, v_x_657_);
                v___x_685_ = 1;
                v___x_686_ = l_Lean_Meta_mkLambdaFVars(
                    v___x_684_,
                    v_inst_658_,
                    v___x_667_,
                    v___x_668_,
                    v___x_667_,
                    v___x_668_,
                    v___x_685_,
                    v_a_659_,
                    v_a_660_,
                    v_a_661_,
                    v_a_662_,
                );
                crate::leanh::lean_dec_ref(v___x_684_);
                if crate::leanh::lean_obj_tag(v___x_686_) == 0 {
                    v_a_687_ = crate::leanh::lean_ctor_get(v___x_686_, 0);
                    v_isSharedCheck_705_ = (!crate::leanh::lean_is_exclusive(v___x_686_)) as u8;
                    if v_isSharedCheck_705_ == 0 {
                        v___x_689_ = v___x_686_;
                        v_isShared_690_ = v_isSharedCheck_705_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_687_);
                        crate::leanh::lean_dec(v___x_686_);
                        v___x_689_ = crate::leanh::lean_box(0);
                        v_isShared_690_ = v_isSharedCheck_705_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_680_);
                    crate::leanh::lean_dec(v_a_678_);
                    return v___x_686_;
                }
            }
            2 => {
                v___x_691_ = l_Lean_Meta_mkInstPiOfInstForall___closed__9;
                if v_isShared_690_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_689_, 1);
                    crate::leanh::lean_ctor_set(v___x_689_, 0, v_a_678_);
                    v___x_693_ = v___x_689_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_704_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_678_);
                    v___x_693_ = v_reuseFailAlloc_704_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_694_ = crate::leanh::lean_box(0);
                if v_isShared_681_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_680_, 1);
                    crate::leanh::lean_ctor_set(v___x_680_, 0, v_a_687_);
                    v___x_696_ = v___x_680_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_703_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_687_);
                    v___x_696_ = v_reuseFailAlloc_703_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_697_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_698_ = lean_mk_empty_array_with_capacity(v___x_697_);
                v___x_699_ = lean_array_push(v___x_698_, v___x_693_);
                v___x_700_ = lean_array_push(v___x_699_, v___x_694_);
                v___x_701_ = lean_array_push(v___x_700_, v___x_696_);
                v___x_702_ = l_Lean_Meta_mkAppOptM(
                    v___x_691_, v___x_701_, v_a_659_, v_a_660_, v_a_661_, v_a_662_,
                );
                return v___x_702_;
            }
            5 => {
                v___x_712_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_713_ = lean_mk_empty_array_with_capacity(v___x_712_);
                v___x_714_ = lean_array_push(v___x_713_, v_x_657_);
                v___x_715_ = 0;
                v___x_716_ = 1;
                v___x_717_ = l_Lean_Meta_mkLambdaFVars(
                    v___x_714_,
                    v_inst_658_,
                    v___x_715_,
                    v___x_668_,
                    v___x_715_,
                    v___x_668_,
                    v___x_716_,
                    v_a_659_,
                    v_a_660_,
                    v_a_661_,
                    v_a_662_,
                );
                crate::leanh::lean_dec_ref(v___x_714_);
                if crate::leanh::lean_obj_tag(v___x_717_) == 0 {
                    v_a_718_ = crate::leanh::lean_ctor_get(v___x_717_, 0);
                    v_isSharedCheck_736_ = (!crate::leanh::lean_is_exclusive(v___x_717_)) as u8;
                    if v_isSharedCheck_736_ == 0 {
                        v___x_720_ = v___x_717_;
                        v_isShared_721_ = v_isSharedCheck_736_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_718_);
                        crate::leanh::lean_dec(v___x_717_);
                        v___x_720_ = crate::leanh::lean_box(0);
                        v_isShared_721_ = v_isSharedCheck_736_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_710_);
                    crate::leanh::lean_dec(v_a_708_);
                    return v___x_717_;
                }
            }
            6 => {
                v___x_722_ = l_Lean_Meta_mkInstPiOfInstForall___closed__11;
                if v_isShared_721_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_720_, 1);
                    crate::leanh::lean_ctor_set(v___x_720_, 0, v_a_708_);
                    v___x_724_ = v___x_720_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_735_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_708_);
                    v___x_724_ = v_reuseFailAlloc_735_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_725_ = crate::leanh::lean_box(0);
                if v_isShared_711_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_710_, 1);
                    crate::leanh::lean_ctor_set(v___x_710_, 0, v_a_718_);
                    v___x_727_ = v___x_710_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_734_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_718_);
                    v___x_727_ = v_reuseFailAlloc_734_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_728_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_729_ = lean_mk_empty_array_with_capacity(v___x_728_);
                v___x_730_ = lean_array_push(v___x_729_, v___x_724_);
                v___x_731_ = lean_array_push(v___x_730_, v___x_725_);
                v___x_732_ = lean_array_push(v___x_731_, v___x_727_);
                v___x_733_ = l_Lean_Meta_mkAppOptM(
                    v___x_722_, v___x_732_, v_a_659_, v_a_660_, v_a_661_, v_a_662_,
                );
                return v___x_733_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkInstPiOfInstForall___boxed(
    mut v_x_738_: *mut crate::leanh::LeanObject,
    mut v_inst_739_: *mut crate::leanh::LeanObject,
    mut v_a_740_: *mut crate::leanh::LeanObject,
    mut v_a_741_: *mut crate::leanh::LeanObject,
    mut v_a_742_: *mut crate::leanh::LeanObject,
    mut v_a_743_: *mut crate::leanh::LeanObject,
    mut v_a_744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_745_ = l_Lean_Meta_mkInstPiOfInstForall(
        v_x_738_,
        v_inst_739_,
        v_a_740_,
        v_a_741_,
        v_a_742_,
        v_a_743_,
    );
    crate::leanh::lean_dec(v_a_743_);
    crate::leanh::lean_dec_ref(v_a_742_);
    crate::leanh::lean_dec(v_a_741_);
    crate::leanh::lean_dec_ref(v_a_740_);
    return v_res_745_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0(
    mut v_00_u03b1_746_: *mut crate::leanh::LeanObject,
    mut v_msg_747_: *mut crate::leanh::LeanObject,
    mut v___y_748_: *mut crate::leanh::LeanObject,
    mut v___y_749_: *mut crate::leanh::LeanObject,
    mut v___y_750_: *mut crate::leanh::LeanObject,
    mut v___y_751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_753_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(
        v_msg_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_,
    );
    return v___x_753_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___boxed(
    mut v_00_u03b1_754_: *mut crate::leanh::LeanObject,
    mut v_msg_755_: *mut crate::leanh::LeanObject,
    mut v___y_756_: *mut crate::leanh::LeanObject,
    mut v___y_757_: *mut crate::leanh::LeanObject,
    mut v___y_758_: *mut crate::leanh::LeanObject,
    mut v___y_759_: *mut crate::leanh::LeanObject,
    mut v___y_760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_761_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0(
        v_00_u03b1_754_,
        v_msg_755_,
        v___y_756_,
        v___y_757_,
        v___y_758_,
        v___y_759_,
    );
    crate::leanh::lean_dec(v___y_759_);
    crate::leanh::lean_dec_ref(v___y_758_);
    crate::leanh::lean_dec(v___y_757_);
    crate::leanh::lean_dec_ref(v___y_756_);
    return v_res_761_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkInstPiOfInstsForall_spec__0(
    mut v_as_762_: *mut crate::leanh::LeanObject,
    mut v_sz_763_: usize,
    mut v_i_764_: usize,
    mut v_b_765_: *mut crate::leanh::LeanObject,
    mut v___y_766_: *mut crate::leanh::LeanObject,
    mut v___y_767_: *mut crate::leanh::LeanObject,
    mut v___y_768_: *mut crate::leanh::LeanObject,
    mut v___y_769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_771_: u8 = 0;
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: usize = 0;
    let mut v___x_777_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_771_ = lean_usize_dec_lt(v_i_764_, v_sz_763_);
                if v___x_771_ == 0 {
                    v___x_772_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_772_, 0, v_b_765_);
                    return v___x_772_;
                } else {
                    v_a_773_ = lean_array_uget_borrowed(v_as_762_, v_i_764_);
                    crate::leanh::lean_inc(v_a_773_);
                    v___x_774_ = l_Lean_Meta_mkInstPiOfInstForall(
                        v_a_773_, v_b_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_774_) == 0 {
                        v_a_775_ = crate::leanh::lean_ctor_get(v___x_774_, 0);
                        crate::leanh::lean_inc(v_a_775_);
                        crate::leanh::lean_dec_ref_known(v___x_774_, 1);
                        v___x_776_ = 1usize;
                        v___x_777_ = lean_usize_add(v_i_764_, v___x_776_);
                        v_i_764_ = v___x_777_;
                        v_b_765_ = v_a_775_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_774_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkInstPiOfInstsForall_spec__0___boxed(
    mut v_as_779_: *mut crate::leanh::LeanObject,
    mut v_sz_780_: *mut crate::leanh::LeanObject,
    mut v_i_781_: *mut crate::leanh::LeanObject,
    mut v_b_782_: *mut crate::leanh::LeanObject,
    mut v___y_783_: *mut crate::leanh::LeanObject,
    mut v___y_784_: *mut crate::leanh::LeanObject,
    mut v___y_785_: *mut crate::leanh::LeanObject,
    mut v___y_786_: *mut crate::leanh::LeanObject,
    mut v___y_787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_788_: usize = 0;
    let mut v_i_boxed_789_: usize = 0;
    let mut v_res_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_788_ = crate::leanh::lean_unbox_usize(v_sz_780_);
    crate::leanh::lean_dec(v_sz_780_);
    v_i_boxed_789_ = crate::leanh::lean_unbox_usize(v_i_781_);
    crate::leanh::lean_dec(v_i_781_);
    v_res_790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkInstPiOfInstsForall_spec__0(v_as_779_, v_sz_boxed_788_, v_i_boxed_789_, v_b_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
    crate::leanh::lean_dec(v___y_786_);
    crate::leanh::lean_dec_ref(v___y_785_);
    crate::leanh::lean_dec(v___y_784_);
    crate::leanh::lean_dec_ref(v___y_783_);
    crate::leanh::lean_dec_ref(v_as_779_);
    return v_res_790_;
}
pub unsafe fn l_Lean_Meta_mkInstPiOfInstsForall(
    mut v_xs_791_: *mut crate::leanh::LeanObject,
    mut v_inst_792_: *mut crate::leanh::LeanObject,
    mut v_a_793_: *mut crate::leanh::LeanObject,
    mut v_a_794_: *mut crate::leanh::LeanObject,
    mut v_a_795_: *mut crate::leanh::LeanObject,
    mut v_a_796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_799_: usize = 0;
    let mut v___x_800_: usize = 0;
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_798_ = l_Array_reverse___redArg(v_xs_791_);
    v_sz_799_ = lean_array_size(v___x_798_);
    v___x_800_ = 0usize;
    v___x_801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkInstPiOfInstsForall_spec__0(v___x_798_, v_sz_799_, v___x_800_, v_inst_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_);
    crate::leanh::lean_dec_ref(v___x_798_);
    return v___x_801_;
}
pub unsafe fn l_Lean_Meta_mkInstPiOfInstsForall___boxed(
    mut v_xs_802_: *mut crate::leanh::LeanObject,
    mut v_inst_803_: *mut crate::leanh::LeanObject,
    mut v_a_804_: *mut crate::leanh::LeanObject,
    mut v_a_805_: *mut crate::leanh::LeanObject,
    mut v_a_806_: *mut crate::leanh::LeanObject,
    mut v_a_807_: *mut crate::leanh::LeanObject,
    mut v_a_808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_809_ = l_Lean_Meta_mkInstPiOfInstsForall(
        v_xs_802_,
        v_inst_803_,
        v_a_804_,
        v_a_805_,
        v_a_806_,
        v_a_807_,
    );
    crate::leanh::lean_dec(v_a_807_);
    crate::leanh::lean_dec_ref(v_a_806_);
    crate::leanh::lean_dec(v_a_805_);
    crate::leanh::lean_dec_ref(v_a_804_);
    return v_res_809_;
}
pub unsafe fn _init_l_Lean_Meta_mkFixOfMonFun___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_811_ = l_Lean_Meta_mkFixOfMonFun___closed__0;
    v___x_812_ = l_Lean_stringToMessageData(v___x_811_);
    return v___x_812_;
}
pub unsafe fn l_Lean_Meta_mkFixOfMonFun(
    mut v_packedType_823_: *mut crate::leanh::LeanObject,
    mut v_packedInst_824_: *mut crate::leanh::LeanObject,
    mut v_hmono_825_: *mut crate::leanh::LeanObject,
    mut v_a_826_: *mut crate::leanh::LeanObject,
    mut v_a_827_: *mut crate::leanh::LeanObject,
    mut v_a_828_: *mut crate::leanh::LeanObject,
    mut v_a_829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_835_: u8 = 0;
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: u8 = 0;
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_842_: u8 = 0;
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: u8 = 0;
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_865_: u8 = 0;
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_880_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_829_);
                crate::leanh::lean_inc_ref(v_a_828_);
                crate::leanh::lean_inc(v_a_827_);
                crate::leanh::lean_inc_ref(v_a_826_);
                crate::leanh::lean_inc_ref(v_packedInst_824_);
                v___x_831_ =
                    lean_infer_type(v_packedInst_824_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
                if crate::leanh::lean_obj_tag(v___x_831_) == 0 {
                    v_a_832_ = crate::leanh::lean_ctor_get(v___x_831_, 0);
                    v_isSharedCheck_880_ = (!crate::leanh::lean_is_exclusive(v___x_831_)) as u8;
                    if v_isSharedCheck_880_ == 0 {
                        v___x_834_ = v___x_831_;
                        v_isShared_835_ = v_isSharedCheck_880_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_832_);
                        crate::leanh::lean_dec(v___x_831_);
                        v___x_834_ = crate::leanh::lean_box(0);
                        v_isShared_835_ = v_isSharedCheck_880_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_hmono_825_);
                    crate::leanh::lean_dec_ref(v_packedInst_824_);
                    crate::leanh::lean_dec_ref(v_packedType_823_);
                    return v___x_831_;
                }
            }
            1 => {
                v___x_836_ = l_Lean_Meta_mkInstPiOfInstForall___closed__3;
                v___x_837_ = l_Lean_Expr_isAppOf(v_a_832_, v___x_836_);
                crate::leanh::lean_dec(v_a_832_);
                if v___x_837_ == 0 {
                    crate::leanh::lean_inc(v_a_829_);
                    crate::leanh::lean_inc_ref(v_a_828_);
                    crate::leanh::lean_inc(v_a_827_);
                    crate::leanh::lean_inc_ref(v_a_826_);
                    crate::leanh::lean_inc_ref(v_packedInst_824_);
                    v___x_838_ =
                        lean_infer_type(v_packedInst_824_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
                    if crate::leanh::lean_obj_tag(v___x_838_) == 0 {
                        v_a_839_ = crate::leanh::lean_ctor_get(v___x_838_, 0);
                        v_isSharedCheck_865_ = (!crate::leanh::lean_is_exclusive(v___x_838_)) as u8;
                        if v_isSharedCheck_865_ == 0 {
                            v___x_841_ = v___x_838_;
                            v_isShared_842_ = v_isSharedCheck_865_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_839_);
                            crate::leanh::lean_dec(v___x_838_);
                            v___x_841_ = crate::leanh::lean_box(0);
                            v_isShared_842_ = v_isSharedCheck_865_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_834_);
                        crate::leanh::lean_dec_ref(v_hmono_825_);
                        crate::leanh::lean_dec_ref(v_packedInst_824_);
                        crate::leanh::lean_dec_ref(v_packedType_823_);
                        return v___x_838_;
                    }
                } else {
                    v___x_866_ = l_Lean_Meta_mkFixOfMonFun___closed__5;
                    if v_isShared_835_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_834_, 1);
                        crate::leanh::lean_ctor_set(v___x_834_, 0, v_packedType_823_);
                        v___x_868_ = v___x_834_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_879_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_879_, 0, v_packedType_823_);
                        v___x_868_ = v_reuseFailAlloc_879_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_843_ = l_Lean_Meta_mkInstPiOfInstForall___closed__5;
                v___x_844_ = l_Lean_Expr_isAppOf(v_a_839_, v___x_843_);
                crate::leanh::lean_dec(v_a_839_);
                if v___x_844_ == 0 {
                    crate::leanh::lean_del_object(v___x_841_);
                    crate::leanh::lean_del_object(v___x_834_);
                    crate::leanh::lean_dec_ref(v_hmono_825_);
                    crate::leanh::lean_dec_ref(v_packedType_823_);
                    v___x_845_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkFixOfMonFun___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkFixOfMonFun___closed__1_once),
                        _init_l_Lean_Meta_mkFixOfMonFun___closed__1,
                    );
                    v___x_846_ = l_Lean_MessageData_ofExpr(v_packedInst_824_);
                    v___x_847_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_847_, 0, v___x_845_);
                    crate::leanh::lean_ctor_set(v___x_847_, 1, v___x_846_);
                    v___x_848_ =
                        l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(
                            v___x_847_, v_a_826_, v_a_827_, v_a_828_, v_a_829_,
                        );
                    return v___x_848_;
                } else {
                    v___x_849_ = l_Lean_Meta_mkFixOfMonFun___closed__3;
                    if v_isShared_842_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_841_, 1);
                        crate::leanh::lean_ctor_set(v___x_841_, 0, v_packedType_823_);
                        v___x_851_ = v___x_841_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_864_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_864_, 0, v_packedType_823_);
                        v___x_851_ = v_reuseFailAlloc_864_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_835_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_834_, 1);
                    crate::leanh::lean_ctor_set(v___x_834_, 0, v_packedInst_824_);
                    v___x_853_ = v___x_834_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_863_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_863_, 0, v_packedInst_824_);
                    v___x_853_ = v_reuseFailAlloc_863_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_854_ = crate::leanh::lean_box(0);
                v___x_855_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_855_, 0, v_hmono_825_);
                v___x_856_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_857_ = lean_mk_empty_array_with_capacity(v___x_856_);
                v___x_858_ = lean_array_push(v___x_857_, v___x_851_);
                v___x_859_ = lean_array_push(v___x_858_, v___x_853_);
                v___x_860_ = lean_array_push(v___x_859_, v___x_854_);
                v___x_861_ = lean_array_push(v___x_860_, v___x_855_);
                v___x_862_ = l_Lean_Meta_mkAppOptM(
                    v___x_849_, v___x_861_, v_a_826_, v_a_827_, v_a_828_, v_a_829_,
                );
                return v___x_862_;
            }
            5 => {
                v___x_869_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_869_, 0, v_packedInst_824_);
                v___x_870_ = crate::leanh::lean_box(0);
                v___x_871_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_871_, 0, v_hmono_825_);
                v___x_872_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_873_ = lean_mk_empty_array_with_capacity(v___x_872_);
                v___x_874_ = lean_array_push(v___x_873_, v___x_868_);
                v___x_875_ = lean_array_push(v___x_874_, v___x_869_);
                v___x_876_ = lean_array_push(v___x_875_, v___x_870_);
                v___x_877_ = lean_array_push(v___x_876_, v___x_871_);
                v___x_878_ = l_Lean_Meta_mkAppOptM(
                    v___x_866_, v___x_877_, v_a_826_, v_a_827_, v_a_828_, v_a_829_,
                );
                return v___x_878_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkFixOfMonFun___boxed(
    mut v_packedType_881_: *mut crate::leanh::LeanObject,
    mut v_packedInst_882_: *mut crate::leanh::LeanObject,
    mut v_hmono_883_: *mut crate::leanh::LeanObject,
    mut v_a_884_: *mut crate::leanh::LeanObject,
    mut v_a_885_: *mut crate::leanh::LeanObject,
    mut v_a_886_: *mut crate::leanh::LeanObject,
    mut v_a_887_: *mut crate::leanh::LeanObject,
    mut v_a_888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_889_ = l_Lean_Meta_mkFixOfMonFun(
        v_packedType_881_,
        v_packedInst_882_,
        v_hmono_883_,
        v_a_884_,
        v_a_885_,
        v_a_886_,
        v_a_887_,
    );
    crate::leanh::lean_dec(v_a_887_);
    crate::leanh::lean_dec_ref(v_a_886_);
    crate::leanh::lean_dec(v_a_885_);
    crate::leanh::lean_dec_ref(v_a_884_);
    return v_res_889_;
}
pub unsafe fn _init_l_Lean_Meta_toPartialOrder___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_891_ = l_Lean_Meta_toPartialOrder___closed__0;
    v___x_892_ = l_Lean_stringToMessageData(v___x_891_);
    return v___x_892_;
}
pub unsafe fn l_Lean_Meta_toPartialOrder(
    mut v_packedInst_904_: *mut crate::leanh::LeanObject,
    mut v_type_905_: *mut crate::leanh::LeanObject,
    mut v_a_906_: *mut crate::leanh::LeanObject,
    mut v_a_907_: *mut crate::leanh::LeanObject,
    mut v_a_908_: *mut crate::leanh::LeanObject,
    mut v_a_909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_915_: u8 = 0;
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: u8 = 0;
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_922_: u8 = 0;
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: u8 = 0;
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_938_: u8 = 0;
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_948_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_909_);
                crate::leanh::lean_inc_ref(v_a_908_);
                crate::leanh::lean_inc(v_a_907_);
                crate::leanh::lean_inc_ref(v_a_906_);
                crate::leanh::lean_inc_ref(v_packedInst_904_);
                v___x_911_ =
                    lean_infer_type(v_packedInst_904_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
                if crate::leanh::lean_obj_tag(v___x_911_) == 0 {
                    v_a_912_ = crate::leanh::lean_ctor_get(v___x_911_, 0);
                    v_isSharedCheck_948_ = (!crate::leanh::lean_is_exclusive(v___x_911_)) as u8;
                    if v_isSharedCheck_948_ == 0 {
                        v___x_914_ = v___x_911_;
                        v_isShared_915_ = v_isSharedCheck_948_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_912_);
                        crate::leanh::lean_dec(v___x_911_);
                        v___x_914_ = crate::leanh::lean_box(0);
                        v_isShared_915_ = v_isSharedCheck_948_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_type_905_);
                    crate::leanh::lean_dec_ref(v_packedInst_904_);
                    return v___x_911_;
                }
            }
            1 => {
                v___x_916_ = l_Lean_Meta_mkInstPiOfInstForall___closed__3;
                v___x_917_ = l_Lean_Expr_isAppOf(v_a_912_, v___x_916_);
                crate::leanh::lean_dec(v_a_912_);
                if v___x_917_ == 0 {
                    crate::leanh::lean_del_object(v___x_914_);
                    crate::leanh::lean_inc(v_a_909_);
                    crate::leanh::lean_inc_ref(v_a_908_);
                    crate::leanh::lean_inc(v_a_907_);
                    crate::leanh::lean_inc_ref(v_a_906_);
                    crate::leanh::lean_inc_ref(v_packedInst_904_);
                    v___x_918_ =
                        lean_infer_type(v_packedInst_904_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
                    if crate::leanh::lean_obj_tag(v___x_918_) == 0 {
                        v_a_919_ = crate::leanh::lean_ctor_get(v___x_918_, 0);
                        v_isSharedCheck_938_ = (!crate::leanh::lean_is_exclusive(v___x_918_)) as u8;
                        if v_isSharedCheck_938_ == 0 {
                            v___x_921_ = v___x_918_;
                            v_isShared_922_ = v_isSharedCheck_938_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_919_);
                            crate::leanh::lean_dec(v___x_918_);
                            v___x_921_ = crate::leanh::lean_box(0);
                            v_isShared_922_ = v_isSharedCheck_938_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_type_905_);
                        crate::leanh::lean_dec_ref(v_packedInst_904_);
                        return v___x_918_;
                    }
                } else {
                    v___x_939_ = l_Lean_Meta_toPartialOrder___closed__4;
                    if v_isShared_915_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_914_, 1);
                        crate::leanh::lean_ctor_set(v___x_914_, 0, v_packedInst_904_);
                        v___x_941_ = v___x_914_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_947_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_947_, 0, v_packedInst_904_);
                        v___x_941_ = v_reuseFailAlloc_947_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_923_ = l_Lean_Meta_mkInstPiOfInstForall___closed__5;
                v___x_924_ = l_Lean_Expr_isAppOf(v_a_919_, v___x_923_);
                crate::leanh::lean_dec(v_a_919_);
                if v___x_924_ == 0 {
                    crate::leanh::lean_del_object(v___x_921_);
                    crate::leanh::lean_dec(v_type_905_);
                    v___x_925_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_toPartialOrder___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_toPartialOrder___closed__1_once),
                        _init_l_Lean_Meta_toPartialOrder___closed__1,
                    );
                    v___x_926_ = l_Lean_MessageData_ofExpr(v_packedInst_904_);
                    v___x_927_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_927_, 0, v___x_925_);
                    crate::leanh::lean_ctor_set(v___x_927_, 1, v___x_926_);
                    v___x_928_ =
                        l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(
                            v___x_927_, v_a_906_, v_a_907_, v_a_908_, v_a_909_,
                        );
                    return v___x_928_;
                } else {
                    v___x_929_ = l_Lean_Meta_toPartialOrder___closed__3;
                    if v_isShared_922_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_921_, 1);
                        crate::leanh::lean_ctor_set(v___x_921_, 0, v_packedInst_904_);
                        v___x_931_ = v___x_921_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_937_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_937_, 0, v_packedInst_904_);
                        v___x_931_ = v_reuseFailAlloc_937_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_932_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_933_ = lean_mk_empty_array_with_capacity(v___x_932_);
                v___x_934_ = lean_array_push(v___x_933_, v_type_905_);
                v___x_935_ = lean_array_push(v___x_934_, v___x_931_);
                v___x_936_ = l_Lean_Meta_mkAppOptM(
                    v___x_929_, v___x_935_, v_a_906_, v_a_907_, v_a_908_, v_a_909_,
                );
                return v___x_936_;
            }
            4 => {
                v___x_942_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_943_ = lean_mk_empty_array_with_capacity(v___x_942_);
                v___x_944_ = lean_array_push(v___x_943_, v_type_905_);
                v___x_945_ = lean_array_push(v___x_944_, v___x_941_);
                v___x_946_ = l_Lean_Meta_mkAppOptM(
                    v___x_939_, v___x_945_, v_a_906_, v_a_907_, v_a_908_, v_a_909_,
                );
                return v___x_946_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_toPartialOrder___boxed(
    mut v_packedInst_949_: *mut crate::leanh::LeanObject,
    mut v_type_950_: *mut crate::leanh::LeanObject,
    mut v_a_951_: *mut crate::leanh::LeanObject,
    mut v_a_952_: *mut crate::leanh::LeanObject,
    mut v_a_953_: *mut crate::leanh::LeanObject,
    mut v_a_954_: *mut crate::leanh::LeanObject,
    mut v_a_955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_956_ = l_Lean_Meta_toPartialOrder(
        v_packedInst_949_,
        v_type_950_,
        v_a_951_,
        v_a_952_,
        v_a_953_,
        v_a_954_,
    );
    crate::leanh::lean_dec(v_a_954_);
    crate::leanh::lean_dec_ref(v_a_953_);
    crate::leanh::lean_dec(v_a_952_);
    crate::leanh::lean_dec_ref(v_a_951_);
    return v_res_956_;
}
pub unsafe fn _init_l_Lean_Meta_mkInstCCPOPProd___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_962_ = crate::leanh::lean_box(0);
    v___x_963_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_964_ = lean_mk_empty_array_with_capacity(v___x_963_);
    v___x_965_ = lean_array_push(v___x_964_, v___x_962_);
    return v___x_965_;
}
pub unsafe fn _init_l_Lean_Meta_mkInstCCPOPProd___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_966_ = crate::leanh::lean_box(0);
    v___x_967_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkInstCCPOPProd___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkInstCCPOPProd___closed__2_once),
        _init_l_Lean_Meta_mkInstCCPOPProd___closed__2,
    );
    v___x_968_ = lean_array_push(v___x_967_, v___x_966_);
    return v___x_968_;
}
pub unsafe fn l_Lean_Meta_mkInstCCPOPProd(
    mut v_inst_u2081_969_: *mut crate::leanh::LeanObject,
    mut v_inst_u2082_970_: *mut crate::leanh::LeanObject,
    mut v_a_971_: *mut crate::leanh::LeanObject,
    mut v_a_972_: *mut crate::leanh::LeanObject,
    mut v_a_973_: *mut crate::leanh::LeanObject,
    mut v_a_974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_976_ = l_Lean_Meta_mkInstCCPOPProd___closed__1;
    v___x_977_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_977_, 0, v_inst_u2081_969_);
    v___x_978_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_978_, 0, v_inst_u2082_970_);
    v___x_979_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkInstCCPOPProd___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkInstCCPOPProd___closed__3_once),
        _init_l_Lean_Meta_mkInstCCPOPProd___closed__3,
    );
    v___x_980_ = lean_array_push(v___x_979_, v___x_977_);
    v___x_981_ = lean_array_push(v___x_980_, v___x_978_);
    v___x_982_ = l_Lean_Meta_mkAppOptM(
        v___x_976_, v___x_981_, v_a_971_, v_a_972_, v_a_973_, v_a_974_,
    );
    return v___x_982_;
}
pub unsafe fn l_Lean_Meta_mkInstCCPOPProd___boxed(
    mut v_inst_u2081_983_: *mut crate::leanh::LeanObject,
    mut v_inst_u2082_984_: *mut crate::leanh::LeanObject,
    mut v_a_985_: *mut crate::leanh::LeanObject,
    mut v_a_986_: *mut crate::leanh::LeanObject,
    mut v_a_987_: *mut crate::leanh::LeanObject,
    mut v_a_988_: *mut crate::leanh::LeanObject,
    mut v_a_989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_990_ = l_Lean_Meta_mkInstCCPOPProd(
        v_inst_u2081_983_,
        v_inst_u2082_984_,
        v_a_985_,
        v_a_986_,
        v_a_987_,
        v_a_988_,
    );
    crate::leanh::lean_dec(v_a_988_);
    crate::leanh::lean_dec_ref(v_a_987_);
    crate::leanh::lean_dec(v_a_986_);
    crate::leanh::lean_dec_ref(v_a_985_);
    return v_res_990_;
}
pub unsafe fn l_Lean_Meta_mkInstCompleteLatticePProd(
    mut v_inst_u2081_996_: *mut crate::leanh::LeanObject,
    mut v_inst_u2082_997_: *mut crate::leanh::LeanObject,
    mut v_a_998_: *mut crate::leanh::LeanObject,
    mut v_a_999_: *mut crate::leanh::LeanObject,
    mut v_a_1000_: *mut crate::leanh::LeanObject,
    mut v_a_1001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1003_ = l_Lean_Meta_mkInstCompleteLatticePProd___closed__1;
    v___x_1004_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1004_, 0, v_inst_u2081_996_);
    v___x_1005_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1005_, 0, v_inst_u2082_997_);
    v___x_1006_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkInstCCPOPProd___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkInstCCPOPProd___closed__3_once),
        _init_l_Lean_Meta_mkInstCCPOPProd___closed__3,
    );
    v___x_1007_ = lean_array_push(v___x_1006_, v___x_1004_);
    v___x_1008_ = lean_array_push(v___x_1007_, v___x_1005_);
    v___x_1009_ = l_Lean_Meta_mkAppOptM(
        v___x_1003_,
        v___x_1008_,
        v_a_998_,
        v_a_999_,
        v_a_1000_,
        v_a_1001_,
    );
    return v___x_1009_;
}
pub unsafe fn l_Lean_Meta_mkInstCompleteLatticePProd___boxed(
    mut v_inst_u2081_1010_: *mut crate::leanh::LeanObject,
    mut v_inst_u2082_1011_: *mut crate::leanh::LeanObject,
    mut v_a_1012_: *mut crate::leanh::LeanObject,
    mut v_a_1013_: *mut crate::leanh::LeanObject,
    mut v_a_1014_: *mut crate::leanh::LeanObject,
    mut v_a_1015_: *mut crate::leanh::LeanObject,
    mut v_a_1016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1017_ = l_Lean_Meta_mkInstCompleteLatticePProd(
        v_inst_u2081_1010_,
        v_inst_u2082_1011_,
        v_a_1012_,
        v_a_1013_,
        v_a_1014_,
        v_a_1015_,
    );
    crate::leanh::lean_dec(v_a_1015_);
    crate::leanh::lean_dec_ref(v_a_1014_);
    crate::leanh::lean_dec(v_a_1013_);
    crate::leanh::lean_dec_ref(v_a_1012_);
    return v_res_1017_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_mkPackedPPRodInstance_spec__3(
    mut v_a_1018_: *mut crate::leanh::LeanObject,
    mut v_a_1019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1025_: u8 = 0;
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1031_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1018_) == 0 {
                    v___x_1020_ = l_List_reverse___redArg(v_a_1019_);
                    return v___x_1020_;
                } else {
                    v_head_1021_ = crate::leanh::lean_ctor_get(v_a_1018_, 0);
                    v_tail_1022_ = crate::leanh::lean_ctor_get(v_a_1018_, 1);
                    v_isSharedCheck_1031_ = (!crate::leanh::lean_is_exclusive(v_a_1018_)) as u8;
                    if v_isSharedCheck_1031_ == 0 {
                        v___x_1024_ = v_a_1018_;
                        v_isShared_1025_ = v_isSharedCheck_1031_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1022_);
                        crate::leanh::lean_inc(v_head_1021_);
                        crate::leanh::lean_dec(v_a_1018_);
                        v___x_1024_ = crate::leanh::lean_box(0);
                        v_isShared_1025_ = v_isSharedCheck_1031_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1026_ = l_Lean_MessageData_ofExpr(v_head_1021_);
                if v_isShared_1025_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1024_, 1, v_a_1019_);
                    crate::leanh::lean_ctor_set(v___x_1024_, 0, v___x_1026_);
                    v___x_1028_ = v___x_1024_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1030_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1026_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_a_1019_);
                    v___x_1028_ = v_reuseFailAlloc_1030_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1018_ = v_tail_1022_;
                v_a_1019_ = v___x_1028_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkPackedPPRodInstance_spec__0(
    mut v_sz_1032_: usize,
    mut v_i_1033_: usize,
    mut v_bs_1034_: *mut crate::leanh::LeanObject,
    mut v___y_1035_: *mut crate::leanh::LeanObject,
    mut v___y_1036_: *mut crate::leanh::LeanObject,
    mut v___y_1037_: *mut crate::leanh::LeanObject,
    mut v___y_1038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1040_: u8 = 0;
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: usize = 0;
    let mut v___x_1048_: usize = 0;
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1054_: u8 = 0;
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1058_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1040_ = lean_usize_dec_lt(v_i_1033_, v_sz_1032_);
                if v___x_1040_ == 0 {
                    v___x_1041_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1041_, 0, v_bs_1034_);
                    return v___x_1041_;
                } else {
                    v_v_1042_ = lean_array_uget_borrowed(v_bs_1034_, v_i_1033_);
                    crate::leanh::lean_inc(v___y_1038_);
                    crate::leanh::lean_inc_ref(v___y_1037_);
                    crate::leanh::lean_inc(v___y_1036_);
                    crate::leanh::lean_inc_ref(v___y_1035_);
                    crate::leanh::lean_inc(v_v_1042_);
                    v___x_1043_ = lean_infer_type(
                        v_v_1042_,
                        v___y_1035_,
                        v___y_1036_,
                        v___y_1037_,
                        v___y_1038_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1043_) == 0 {
                        v_a_1044_ = crate::leanh::lean_ctor_get(v___x_1043_, 0);
                        crate::leanh::lean_inc(v_a_1044_);
                        crate::leanh::lean_dec_ref_known(v___x_1043_, 1);
                        v___x_1045_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1046_ = lean_array_uset(v_bs_1034_, v_i_1033_, v___x_1045_);
                        v___x_1047_ = 1usize;
                        v___x_1048_ = lean_usize_add(v_i_1033_, v___x_1047_);
                        v___x_1049_ = lean_array_uset(v_bs_x27_1046_, v_i_1033_, v_a_1044_);
                        v_i_1033_ = v___x_1048_;
                        v_bs_1034_ = v___x_1049_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_1034_);
                        v_a_1051_ = crate::leanh::lean_ctor_get(v___x_1043_, 0);
                        v_isSharedCheck_1058_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1043_)) as u8;
                        if v_isSharedCheck_1058_ == 0 {
                            v___x_1053_ = v___x_1043_;
                            v_isShared_1054_ = v_isSharedCheck_1058_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1051_);
                            crate::leanh::lean_dec(v___x_1043_);
                            v___x_1053_ = crate::leanh::lean_box(0);
                            v_isShared_1054_ = v_isSharedCheck_1058_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1054_ == 0 {
                    v___x_1056_ = v___x_1053_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1057_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
                    v___x_1056_ = v_reuseFailAlloc_1057_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1056_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkPackedPPRodInstance_spec__0___boxed(
    mut v_sz_1059_: *mut crate::leanh::LeanObject,
    mut v_i_1060_: *mut crate::leanh::LeanObject,
    mut v_bs_1061_: *mut crate::leanh::LeanObject,
    mut v___y_1062_: *mut crate::leanh::LeanObject,
    mut v___y_1063_: *mut crate::leanh::LeanObject,
    mut v___y_1064_: *mut crate::leanh::LeanObject,
    mut v___y_1065_: *mut crate::leanh::LeanObject,
    mut v___y_1066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1067_: usize = 0;
    let mut v_i_boxed_1068_: usize = 0;
    let mut v_res_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1067_ = crate::leanh::lean_unbox_usize(v_sz_1059_);
    crate::leanh::lean_dec(v_sz_1059_);
    v_i_boxed_1068_ = crate::leanh::lean_unbox_usize(v_i_1060_);
    crate::leanh::lean_dec(v_i_1060_);
    v_res_1069_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkPackedPPRodInstance_spec__0(v_sz_boxed_1067_, v_i_boxed_1068_, v_bs_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
    crate::leanh::lean_dec(v___y_1065_);
    crate::leanh::lean_dec_ref(v___y_1064_);
    crate::leanh::lean_dec(v___y_1063_);
    crate::leanh::lean_dec_ref(v___y_1062_);
    return v_res_1069_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__1(
    mut v_as_1070_: *mut crate::leanh::LeanObject,
    mut v_i_1071_: usize,
    mut v_stop_1072_: usize,
) -> u8 {
    let mut v___x_1073_: u8 = 0;
    let mut v___x_1074_: u8 = 0;
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: u8 = 0;
    let mut v___x_1078_: usize = 0;
    let mut v___x_1079_: usize = 0;
    let mut v___x_1081_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1073_ = lean_usize_dec_eq(v_i_1071_, v_stop_1072_);
                if v___x_1073_ == 0 {
                    v___x_1074_ = 1;
                    v___x_1075_ = lean_array_uget_borrowed(v_as_1070_, v_i_1071_);
                    v___x_1076_ = l_Lean_Meta_mkInstPiOfInstForall___closed__3;
                    v___x_1077_ = l_Lean_Expr_isAppOf(v___x_1075_, v___x_1076_);
                    if v___x_1077_ == 0 {
                        return v___x_1074_;
                    } else {
                        if v___x_1073_ == 0 {
                            v___x_1078_ = 1usize;
                            v___x_1079_ = lean_usize_add(v_i_1071_, v___x_1078_);
                            v_i_1071_ = v___x_1079_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_1074_;
                        }
                    }
                } else {
                    v___x_1081_ = 0;
                    return v___x_1081_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__1___boxed(
    mut v_as_1082_: *mut crate::leanh::LeanObject,
    mut v_i_1083_: *mut crate::leanh::LeanObject,
    mut v_stop_1084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1085_: usize = 0;
    let mut v_stop_boxed_1086_: usize = 0;
    let mut v_res_1087_: u8 = 0;
    let mut v_r_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1085_ = crate::leanh::lean_unbox_usize(v_i_1083_);
    crate::leanh::lean_dec(v_i_1083_);
    v_stop_boxed_1086_ = crate::leanh::lean_unbox_usize(v_stop_1084_);
    crate::leanh::lean_dec(v_stop_1084_);
    v_res_1087_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__1(v_as_1082_, v_i_boxed_1085_, v_stop_boxed_1086_);
    crate::leanh::lean_dec_ref(v_as_1082_);
    v_r_1088_ = crate::leanh::lean_box((v_res_1087_) as usize);
    return v_r_1088_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__2(
    mut v___x_1089_: u8,
    mut v_as_1090_: *mut crate::leanh::LeanObject,
    mut v_i_1091_: usize,
    mut v_stop_1092_: usize,
) -> u8 {
    let mut v___x_1094_: usize = 0;
    let mut v___x_1095_: usize = 0;
    let mut v___x_1097_: u8 = 0;
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: u8 = 0;
    let mut v___x_1101_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1097_ = lean_usize_dec_eq(v_i_1091_, v_stop_1092_);
                if v___x_1097_ == 0 {
                    v___x_1098_ = lean_array_uget_borrowed(v_as_1090_, v_i_1091_);
                    v___x_1099_ = l_Lean_Meta_mkInstPiOfInstForall___closed__5;
                    v___x_1100_ = l_Lean_Expr_isAppOf(v___x_1098_, v___x_1099_);
                    if v___x_1100_ == 0 {
                        if v___x_1089_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            return v___x_1089_;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1101_ = 0;
                    return v___x_1101_;
                }
            }
            1 => {
                v___x_1094_ = 1usize;
                v___x_1095_ = lean_usize_add(v_i_1091_, v___x_1094_);
                v_i_1091_ = v___x_1095_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__2___boxed(
    mut v___x_1102_: *mut crate::leanh::LeanObject,
    mut v_as_1103_: *mut crate::leanh::LeanObject,
    mut v_i_1104_: *mut crate::leanh::LeanObject,
    mut v_stop_1105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1493__boxed_1106_: u8 = 0;
    let mut v_i_boxed_1107_: usize = 0;
    let mut v_stop_boxed_1108_: usize = 0;
    let mut v_res_1109_: u8 = 0;
    let mut v_r_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1493__boxed_1106_ = (crate::leanh::lean_unbox(v___x_1102_) as u8);
    v_i_boxed_1107_ = crate::leanh::lean_unbox_usize(v_i_1104_);
    crate::leanh::lean_dec(v_i_1104_);
    v_stop_boxed_1108_ = crate::leanh::lean_unbox_usize(v_stop_1105_);
    crate::leanh::lean_dec(v_stop_1105_);
    v_res_1109_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__2(v___x_1493__boxed_1106_, v_as_1103_, v_i_boxed_1107_, v_stop_boxed_1108_);
    crate::leanh::lean_dec_ref(v_as_1103_);
    v_r_1110_ = crate::leanh::lean_box((v_res_1109_) as usize);
    return v_r_1110_;
}
pub unsafe fn _init_l_Lean_Meta_mkPackedPPRodInstance___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1114_ = l_Lean_Meta_mkPackedPPRodInstance___closed__2;
    v___x_1115_ = l_Lean_stringToMessageData(v___x_1114_);
    return v___x_1115_;
}
pub unsafe fn _init_l_Lean_Meta_mkPackedPPRodInstance___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1117_ = l_Lean_Meta_mkPackedPPRodInstance___closed__4;
    v___x_1118_ = l_Lean_stringToMessageData(v___x_1117_);
    return v___x_1118_;
}
pub unsafe fn l_Lean_Meta_mkPackedPPRodInstance(
    mut v_insts_1119_: *mut crate::leanh::LeanObject,
    mut v_a_1120_: *mut crate::leanh::LeanObject,
    mut v_a_1121_: *mut crate::leanh::LeanObject,
    mut v_a_1122_: *mut crate::leanh::LeanObject,
    mut v_a_1123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_1125_: usize = 0;
    let mut v___x_1126_: usize = 0;
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: u8 = 0;
    let mut v___x_1140_: usize = 0;
    let mut v___x_1141_: u8 = 0;
    let mut v___x_1142_: u8 = 0;
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1159_: u8 = 0;
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1163_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_1125_ = lean_array_size(v_insts_1119_);
                v___x_1126_ = 0usize;
                crate::leanh::lean_inc_ref(v_insts_1119_);
                v___x_1127_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkPackedPPRodInstance_spec__0(v_sz_1125_, v___x_1126_, v_insts_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
                if crate::leanh::lean_obj_tag(v___x_1127_) == 0 {
                    v_a_1128_ = crate::leanh::lean_ctor_get(v___x_1127_, 0);
                    crate::leanh::lean_inc(v_a_1128_);
                    crate::leanh::lean_dec_ref_known(v___x_1127_, 1);
                    v___x_1137_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1138_ = lean_array_get_size(v_a_1128_);
                    v___x_1139_ = lean_nat_dec_lt(v___x_1137_, v___x_1138_);
                    if v___x_1139_ == 0 {
                        crate::leanh::lean_dec(v_a_1128_);
                        state = 2;
                        continue;
                    } else {
                        if v___x_1139_ == 0 {
                            crate::leanh::lean_dec(v_a_1128_);
                            state = 2;
                            continue;
                        } else {
                            v___x_1140_ = lean_usize_of_nat(v___x_1138_);
                            v___x_1141_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__1(v_a_1128_, v___x_1126_, v___x_1140_);
                            if v___x_1141_ == 0 {
                                crate::leanh::lean_dec(v_a_1128_);
                                state = 2;
                                continue;
                            } else {
                                if v___x_1139_ == 0 {
                                    crate::leanh::lean_dec(v_a_1128_);
                                    state = 1;
                                    continue;
                                } else {
                                    if v___x_1139_ == 0 {
                                        crate::leanh::lean_dec(v_a_1128_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_1142_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__2(v___x_1141_, v_a_1128_, v___x_1126_, v___x_1140_);
                                        if v___x_1142_ == 0 {
                                            crate::leanh::lean_dec(v_a_1128_);
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_1143_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_mkPackedPPRodInstance___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_mkPackedPPRodInstance___closed__3_once), _init_l_Lean_Meta_mkPackedPPRodInstance___closed__3);
                                            v___x_1144_ = lean_array_to_list(v_a_1128_);
                                            v___x_1145_ = crate::leanh::lean_box(0);
                                            v___x_1146_ = l_List_mapTR_loop___at___00Lean_Meta_mkPackedPPRodInstance_spec__3(v___x_1144_, v___x_1145_);
                                            v___x_1147_ = l_Lean_MessageData_ofList(v___x_1146_);
                                            v___x_1148_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_1148_,
                                                0,
                                                v___x_1143_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_1148_,
                                                1,
                                                v___x_1147_,
                                            );
                                            v___x_1149_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_mkPackedPPRodInstance___closed__5), core::ptr::addr_of_mut!(l_Lean_Meta_mkPackedPPRodInstance___closed__5_once), _init_l_Lean_Meta_mkPackedPPRodInstance___closed__5);
                                            v___x_1150_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_1150_,
                                                0,
                                                v___x_1148_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_1150_,
                                                1,
                                                v___x_1149_,
                                            );
                                            v___x_1151_ = lean_array_to_list(v_insts_1119_);
                                            v___x_1152_ = l_List_mapTR_loop___at___00Lean_Meta_mkPackedPPRodInstance_spec__3(v___x_1151_, v___x_1145_);
                                            v___x_1153_ = l_Lean_MessageData_ofList(v___x_1152_);
                                            v___x_1154_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_1154_,
                                                0,
                                                v___x_1150_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_1154_,
                                                1,
                                                v___x_1153_,
                                            );
                                            v___x_1155_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(v___x_1154_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
                                            return v___x_1155_;
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_insts_1119_);
                    v_a_1156_ = crate::leanh::lean_ctor_get(v___x_1127_, 0);
                    v_isSharedCheck_1163_ = (!crate::leanh::lean_is_exclusive(v___x_1127_)) as u8;
                    if v_isSharedCheck_1163_ == 0 {
                        v___x_1158_ = v___x_1127_;
                        v_isShared_1159_ = v_isSharedCheck_1163_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1156_);
                        crate::leanh::lean_dec(v___x_1127_);
                        v___x_1158_ = crate::leanh::lean_box(0);
                        v_isShared_1159_ = v_isSharedCheck_1163_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1130_ = l_Lean_instInhabitedExpr;
                v___x_1131_ = l_Lean_Meta_mkPackedPPRodInstance___closed__0;
                v___x_1132_ = l_Lean_Meta_PProdN_genMk___redArg(
                    v___x_1130_,
                    v___x_1131_,
                    v_insts_1119_,
                    v_a_1120_,
                    v_a_1121_,
                    v_a_1122_,
                    v_a_1123_,
                );
                return v___x_1132_;
            }
            2 => {
                v___x_1134_ = l_Lean_instInhabitedExpr;
                v___x_1135_ = l_Lean_Meta_mkPackedPPRodInstance___closed__1;
                v___x_1136_ = l_Lean_Meta_PProdN_genMk___redArg(
                    v___x_1134_,
                    v___x_1135_,
                    v_insts_1119_,
                    v_a_1120_,
                    v_a_1121_,
                    v_a_1122_,
                    v_a_1123_,
                );
                return v___x_1136_;
            }
            3 => {
                if v_isShared_1159_ == 0 {
                    v___x_1161_ = v___x_1158_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1162_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
                    v___x_1161_ = v_reuseFailAlloc_1162_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1161_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkPackedPPRodInstance___boxed(
    mut v_insts_1164_: *mut crate::leanh::LeanObject,
    mut v_a_1165_: *mut crate::leanh::LeanObject,
    mut v_a_1166_: *mut crate::leanh::LeanObject,
    mut v_a_1167_: *mut crate::leanh::LeanObject,
    mut v_a_1168_: *mut crate::leanh::LeanObject,
    mut v_a_1169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1170_ = l_Lean_Meta_mkPackedPPRodInstance(
        v_insts_1164_,
        v_a_1165_,
        v_a_1166_,
        v_a_1167_,
        v_a_1168_,
    );
    crate::leanh::lean_dec(v_a_1168_);
    crate::leanh::lean_dec_ref(v_a_1167_);
    crate::leanh::lean_dec(v_a_1166_);
    crate::leanh::lean_dec_ref(v_a_1165_);
    return v_res_1170_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Order(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_PProdN(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Internal_Order_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Order(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Order(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_PProdN(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Internal_Order_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Order(builtin);
}
