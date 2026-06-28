// Lean compiler output
// Module: Lean.Meta.Order
// Imports: Lean.Meta.PProdN Lean.Meta.AppBuilder Init.Internal.Order.Basic
use crate::r#gen::Init::Data::Array::Basic::l_Array_reverse___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Internal::Order::Basic::{
    initialize_Init_Internal_Order_Basic, runtime_initialize_Init_Internal_Order_Basic,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr3, l_Lean_Name_mkStr4};
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_mkInstPiOfInstForall___closed__0_value: LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_mkInstPiOfInstForall___closed__1_value: LeanStringObject<6> =
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
        m_data: [79, 114, 100, 101, 114, 0],
    };
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_mkInstPiOfInstForall___closed__2_value: LeanStringObject<5> =
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
        m_data: [67, 67, 80, 79, 0],
    };
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__2_value) as *mut LeanObject;
static l_Lean_Meta_mkInstPiOfInstForall___closed__3_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_mkInstPiOfInstForall___closed__3_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__1_value)
                as *mut LeanObject,
            489434913524309295 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_mkInstPiOfInstForall___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__3_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__2_value) as *mut LeanObject,
        14719117893866890003 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_mkInstPiOfInstForall___closed__4_value: LeanStringObject<16> =
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
            67, 111, 109, 112, 108, 101, 116, 101, 76, 97, 116, 116, 105, 99, 101, 0,
        ],
    };
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__4_value) as *mut LeanObject;
static l_Lean_Meta_mkInstPiOfInstForall___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_mkInstPiOfInstForall___closed__5_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__5_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__1_value)
                as *mut LeanObject,
            489434913524309295 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_mkInstPiOfInstForall___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__5_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__4_value) as *mut LeanObject,
        7757046375493111023 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__5_value) as *mut LeanObject;
pub static l_Lean_Meta_mkInstPiOfInstForall___closed__6_value: LeanStringObject<42> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__6_value) as *mut LeanObject;
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkInstPiOfInstForall___closed__8_value: LeanStringObject<22> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__8_value) as *mut LeanObject;
static l_Lean_Meta_mkInstPiOfInstForall___closed__9_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_mkInstPiOfInstForall___closed__9_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__9_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__1_value)
                as *mut LeanObject,
            489434913524309295 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_mkInstPiOfInstForall___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__9_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__8_value) as *mut LeanObject,
        2333849305392694232 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__9_value) as *mut LeanObject;
pub static l_Lean_Meta_mkInstPiOfInstForall___closed__10_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__10_value) as *mut LeanObject;
static l_Lean_Meta_mkInstPiOfInstForall___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_mkInstPiOfInstForall___closed__11_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__11_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__1_value)
                as *mut LeanObject,
            489434913524309295 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_mkInstPiOfInstForall___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__11_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__10_value)
                as *mut LeanObject,
            16137463000135501002 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_mkInstPiOfInstForall___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__11_value) as *mut LeanObject;
pub static l_Lean_Meta_mkFixOfMonFun___closed__0_value: LeanStringObject<35> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        109, 107, 70, 105, 120, 79, 102, 77, 111, 110, 70, 117, 110, 58, 32, 117, 110, 101, 120,
        112, 101, 99, 116, 101, 100, 32, 116, 121, 112, 101, 32, 111, 102, 32, 0,
    ],
};
static mut l_Lean_Meta_mkFixOfMonFun___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkFixOfMonFun___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_mkFixOfMonFun___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkFixOfMonFun___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkFixOfMonFun___closed__2_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_mkFixOfMonFun___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkFixOfMonFun___closed__2_value) as *mut LeanObject;
static l_Lean_Meta_mkFixOfMonFun___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Meta_mkFixOfMonFun___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkFixOfMonFun___closed__3_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__1_value) as *mut LeanObject,
        489434913524309295 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_mkFixOfMonFun___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkFixOfMonFun___closed__3_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkFixOfMonFun___closed__2_value) as *mut LeanObject,
        2249643242235982818 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkFixOfMonFun___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkFixOfMonFun___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_mkFixOfMonFun___closed__4_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_mkFixOfMonFun___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkFixOfMonFun___closed__4_value) as *mut LeanObject;
static l_Lean_Meta_mkFixOfMonFun___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Meta_mkFixOfMonFun___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkFixOfMonFun___closed__5_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__1_value) as *mut LeanObject,
        489434913524309295 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_mkFixOfMonFun___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkFixOfMonFun___closed__5_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkFixOfMonFun___closed__4_value) as *mut LeanObject,
        1180902349914728466 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkFixOfMonFun___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkFixOfMonFun___closed__5_value) as *mut LeanObject;
pub static l_Lean_Meta_toPartialOrder___closed__0_value: LeanStringObject<40> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        103, 101, 116, 85, 110, 100, 101, 114, 108, 121, 105, 110, 103, 79, 114, 100, 101, 114, 58,
        32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 121, 112, 101, 32, 111, 102,
        32, 0,
    ],
};
static mut l_Lean_Meta_toPartialOrder___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_toPartialOrder___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_toPartialOrder___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_toPartialOrder___closed__2_value: LeanStringObject<15> = LeanStringObject {
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
        116, 111, 80, 97, 114, 116, 105, 97, 108, 79, 114, 100, 101, 114, 0,
    ],
};
static mut l_Lean_Meta_toPartialOrder___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__2_value) as *mut LeanObject;
static l_Lean_Meta_toPartialOrder___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Meta_toPartialOrder___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__3_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__1_value) as *mut LeanObject,
        489434913524309295 as *mut LeanObject,
    ],
};
static l_Lean_Meta_toPartialOrder___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__3_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__4_value) as *mut LeanObject,
        7757046375493111023 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_toPartialOrder___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__3_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__2_value) as *mut LeanObject,
        17628181181762307085 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_toPartialOrder___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__3_value) as *mut LeanObject;
static l_Lean_Meta_toPartialOrder___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Meta_toPartialOrder___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__4_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__1_value) as *mut LeanObject,
        489434913524309295 as *mut LeanObject,
    ],
};
static l_Lean_Meta_toPartialOrder___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__4_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__2_value) as *mut LeanObject,
        14719117893866890003 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_toPartialOrder___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__4_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__2_value) as *mut LeanObject,
        3289060660584192201 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_toPartialOrder___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_toPartialOrder___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_mkInstCCPOPProd___closed__0_value: LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_mkInstCCPOPProd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstCCPOPProd___closed__0_value) as *mut LeanObject;
static l_Lean_Meta_mkInstCCPOPProd___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Meta_mkInstCCPOPProd___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkInstCCPOPProd___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__1_value) as *mut LeanObject,
        489434913524309295 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_mkInstCCPOPProd___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_mkInstCCPOPProd___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_mkInstCCPOPProd___closed__0_value) as *mut LeanObject,
        17323779659096317889 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkInstCCPOPProd___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstCCPOPProd___closed__1_value) as *mut LeanObject;
static mut l_Lean_Meta_mkInstCCPOPProd___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkInstCCPOPProd___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_mkInstCCPOPProd___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkInstCCPOPProd___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkInstCompleteLatticePProd___closed__0_value: LeanStringObject<25> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            105, 110, 115, 116, 67, 111, 109, 112, 108, 101, 116, 101, 76, 97, 116, 116, 105, 99,
            101, 80, 80, 114, 111, 100, 0,
        ],
    };
static mut l_Lean_Meta_mkInstCompleteLatticePProd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstCompleteLatticePProd___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_mkInstCompleteLatticePProd___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_mkInstCompleteLatticePProd___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstCompleteLatticePProd___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstPiOfInstForall___closed__1_value)
                as *mut LeanObject,
            489434913524309295 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_mkInstCompleteLatticePProd___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkInstCompleteLatticePProd___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkInstCompleteLatticePProd___closed__0_value)
                as *mut LeanObject,
            14055657004040094196 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_mkInstCompleteLatticePProd___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkInstCompleteLatticePProd___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_mkPackedPPRodInstance___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_mkInstCompleteLatticePProd___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_mkPackedPPRodInstance___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkPackedPPRodInstance___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_mkPackedPPRodInstance___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_mkInstCCPOPProd___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_mkPackedPPRodInstance___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkPackedPPRodInstance___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_mkPackedPPRodInstance___closed__2_value: LeanStringObject<42> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_mkPackedPPRodInstance___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkPackedPPRodInstance___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_mkPackedPPRodInstance___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkPackedPPRodInstance___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkPackedPPRodInstance___closed__4_value: LeanStringObject<5> =
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
        m_data: [32, 111, 102, 32, 0],
    };
static mut l_Lean_Meta_mkPackedPPRodInstance___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkPackedPPRodInstance___closed__4_value) as *mut LeanObject;
static mut l_Lean_Meta_mkPackedPPRodInstance___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkPackedPPRodInstance___closed__5: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0_spec__0(
    mut v_msgData_586_: *mut LeanObject,
    mut v___y_587_: *mut LeanObject,
    mut v___y_588_: *mut LeanObject,
    mut v___y_589_: *mut LeanObject,
    mut v___y_590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    v___x_592_ = lean_st_ref_get(v___y_590_);
    v_env_593_ = lean_ctor_get(v___x_592_, 0);
    lean_inc_ref(v_env_593_);
    lean_dec(v___x_592_);
    v___x_594_ = lean_st_ref_get(v___y_588_);
    v_mctx_595_ = lean_ctor_get(v___x_594_, 0);
    lean_inc_ref(v_mctx_595_);
    lean_dec(v___x_594_);
    v_lctx_596_ = lean_ctor_get(v___y_587_, 2);
    v_options_597_ = lean_ctor_get(v___y_589_, 2);
    lean_inc_ref(v_options_597_);
    lean_inc_ref(v_lctx_596_);
    v___x_598_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_598_, 0, v_env_593_);
    lean_ctor_set(v___x_598_, 1, v_mctx_595_);
    lean_ctor_set(v___x_598_, 2, v_lctx_596_);
    lean_ctor_set(v___x_598_, 3, v_options_597_);
    v___x_599_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_599_, 0, v___x_598_);
    lean_ctor_set(v___x_599_, 1, v_msgData_586_);
    v___x_600_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_600_, 0, v___x_599_);
    return v___x_600_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0_spec__0___boxed(
    mut v_msgData_601_: *mut LeanObject,
    mut v___y_602_: *mut LeanObject,
    mut v___y_603_: *mut LeanObject,
    mut v___y_604_: *mut LeanObject,
    mut v___y_605_: *mut LeanObject,
    mut v___y_606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_607_: *mut LeanObject = core::ptr::null_mut();
    v_res_607_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0_spec__0(v_msgData_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
    lean_dec(v___y_605_);
    lean_dec_ref(v___y_604_);
    lean_dec(v___y_603_);
    lean_dec_ref(v___y_602_);
    return v_res_607_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(
    mut v_msg_608_: *mut LeanObject,
    mut v___y_609_: *mut LeanObject,
    mut v___y_610_: *mut LeanObject,
    mut v___y_611_: *mut LeanObject,
    mut v___y_612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_619_: u8 = 0;
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_624_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_614_ = lean_ctor_get(v___y_611_, 5);
                v___x_615_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0_spec__0(v_msg_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
                v_a_616_ = lean_ctor_get(v___x_615_, 0);
                v_isSharedCheck_624_ = (!lean_is_exclusive(v___x_615_)) as u8;
                if v_isSharedCheck_624_ == 0 {
                    v___x_618_ = v___x_615_;
                    v_isShared_619_ = v_isSharedCheck_624_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_616_);
                    lean_dec(v___x_615_);
                    v___x_618_ = lean_box(0);
                    v_isShared_619_ = v_isSharedCheck_624_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_614_);
                v___x_620_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_620_, 0, v_ref_614_);
                lean_ctor_set(v___x_620_, 1, v_a_616_);
                if v_isShared_619_ == 0 {
                    lean_ctor_set_tag(v___x_618_, 1);
                    lean_ctor_set(v___x_618_, 0, v___x_620_);
                    v___x_622_ = v___x_618_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
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
    mut v_msg_625_: *mut LeanObject,
    mut v___y_626_: *mut LeanObject,
    mut v___y_627_: *mut LeanObject,
    mut v___y_628_: *mut LeanObject,
    mut v___y_629_: *mut LeanObject,
    mut v___y_630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_631_: *mut LeanObject = core::ptr::null_mut();
    v_res_631_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(
        v_msg_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_,
    );
    lean_dec(v___y_629_);
    lean_dec_ref(v___y_628_);
    lean_dec(v___y_627_);
    lean_dec_ref(v___y_626_);
    return v_res_631_;
}
pub unsafe fn _init_l_Lean_Meta_mkInstPiOfInstForall___closed__7() -> *mut LeanObject {
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    v___x_645_ = l_Lean_Meta_mkInstPiOfInstForall___closed__6;
    v___x_646_ = l_Lean_stringToMessageData(v___x_645_);
    return v___x_646_;
}
pub unsafe fn l_Lean_Meta_mkInstPiOfInstForall(
    mut v_x_657_: *mut LeanObject,
    mut v_inst_658_: *mut LeanObject,
    mut v_a_659_: *mut LeanObject,
    mut v_a_660_: *mut LeanObject,
    mut v_a_661_: *mut LeanObject,
    mut v_a_662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_667_: u8 = 0;
    let mut v___x_668_: u8 = 0;
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: u8 = 0;
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_681_: u8 = 0;
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: u8 = 0;
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_690_: u8 = 0;
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_705_: u8 = 0;
    let mut v_isSharedCheck_706_: u8 = 0;
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_711_: u8 = 0;
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_715_: u8 = 0;
    let mut v___x_716_: u8 = 0;
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_721_: u8 = 0;
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_736_: u8 = 0;
    let mut v_isSharedCheck_737_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_662_);
                lean_inc_ref(v_a_661_);
                lean_inc(v_a_660_);
                lean_inc_ref(v_a_659_);
                lean_inc_ref(v_inst_658_);
                v___x_664_ = lean_infer_type(v_inst_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
                if lean_obj_tag(v___x_664_) == 0 {
                    v_a_665_ = lean_ctor_get(v___x_664_, 0);
                    lean_inc(v_a_665_);
                    lean_dec_ref_known(v___x_664_, 1);
                    v___x_666_ = l_Lean_Meta_mkInstPiOfInstForall___closed__3;
                    v___x_667_ = l_Lean_Expr_isAppOf(v_a_665_, v___x_666_);
                    lean_dec(v_a_665_);
                    v___x_668_ = 1;
                    if v___x_667_ == 0 {
                        lean_inc(v_a_662_);
                        lean_inc_ref(v_a_661_);
                        lean_inc(v_a_660_);
                        lean_inc_ref(v_a_659_);
                        lean_inc_ref(v_inst_658_);
                        v___x_669_ =
                            lean_infer_type(v_inst_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
                        if lean_obj_tag(v___x_669_) == 0 {
                            v_a_670_ = lean_ctor_get(v___x_669_, 0);
                            lean_inc(v_a_670_);
                            lean_dec_ref_known(v___x_669_, 1);
                            v___x_671_ = l_Lean_Meta_mkInstPiOfInstForall___closed__5;
                            v___x_672_ = l_Lean_Expr_isAppOf(v_a_670_, v___x_671_);
                            lean_dec(v_a_670_);
                            if v___x_672_ == 0 {
                                lean_dec_ref(v_x_657_);
                                v___x_673_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_mkInstPiOfInstForall___closed__7
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_mkInstPiOfInstForall___closed__7_once
                                    ),
                                    _init_l_Lean_Meta_mkInstPiOfInstForall___closed__7,
                                );
                                v___x_674_ = l_Lean_MessageData_ofExpr(v_inst_658_);
                                v___x_675_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_675_, 0, v___x_673_);
                                lean_ctor_set(v___x_675_, 1, v___x_674_);
                                v___x_676_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(v___x_675_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
                                return v___x_676_;
                            } else {
                                lean_inc(v_a_662_);
                                lean_inc_ref(v_a_661_);
                                lean_inc(v_a_660_);
                                lean_inc_ref(v_a_659_);
                                lean_inc_ref(v_x_657_);
                                v___x_677_ = lean_infer_type(
                                    v_x_657_, v_a_659_, v_a_660_, v_a_661_, v_a_662_,
                                );
                                if lean_obj_tag(v___x_677_) == 0 {
                                    v_a_678_ = lean_ctor_get(v___x_677_, 0);
                                    v_isSharedCheck_706_ = (!lean_is_exclusive(v___x_677_)) as u8;
                                    if v_isSharedCheck_706_ == 0 {
                                        v___x_680_ = v___x_677_;
                                        v_isShared_681_ = v_isSharedCheck_706_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_678_);
                                        lean_dec(v___x_677_);
                                        v___x_680_ = lean_box(0);
                                        v_isShared_681_ = v_isSharedCheck_706_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_inst_658_);
                                    lean_dec_ref(v_x_657_);
                                    return v___x_677_;
                                }
                            }
                        } else {
                            lean_dec_ref(v_inst_658_);
                            lean_dec_ref(v_x_657_);
                            return v___x_669_;
                        }
                    } else {
                        lean_inc(v_a_662_);
                        lean_inc_ref(v_a_661_);
                        lean_inc(v_a_660_);
                        lean_inc_ref(v_a_659_);
                        lean_inc_ref(v_x_657_);
                        v___x_707_ =
                            lean_infer_type(v_x_657_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
                        if lean_obj_tag(v___x_707_) == 0 {
                            v_a_708_ = lean_ctor_get(v___x_707_, 0);
                            v_isSharedCheck_737_ = (!lean_is_exclusive(v___x_707_)) as u8;
                            if v_isSharedCheck_737_ == 0 {
                                v___x_710_ = v___x_707_;
                                v_isShared_711_ = v_isSharedCheck_737_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_708_);
                                lean_dec(v___x_707_);
                                v___x_710_ = lean_box(0);
                                v_isShared_711_ = v_isSharedCheck_737_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_inst_658_);
                            lean_dec_ref(v_x_657_);
                            return v___x_707_;
                        }
                    }
                } else {
                    lean_dec_ref(v_inst_658_);
                    lean_dec_ref(v_x_657_);
                    return v___x_664_;
                }
            }
            1 => {
                v___x_682_ = lean_unsigned_to_nat(1);
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
                lean_dec_ref(v___x_684_);
                if lean_obj_tag(v___x_686_) == 0 {
                    v_a_687_ = lean_ctor_get(v___x_686_, 0);
                    v_isSharedCheck_705_ = (!lean_is_exclusive(v___x_686_)) as u8;
                    if v_isSharedCheck_705_ == 0 {
                        v___x_689_ = v___x_686_;
                        v_isShared_690_ = v_isSharedCheck_705_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_687_);
                        lean_dec(v___x_686_);
                        v___x_689_ = lean_box(0);
                        v_isShared_690_ = v_isSharedCheck_705_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_680_);
                    lean_dec(v_a_678_);
                    return v___x_686_;
                }
            }
            2 => {
                v___x_691_ = l_Lean_Meta_mkInstPiOfInstForall___closed__9;
                if v_isShared_690_ == 0 {
                    lean_ctor_set_tag(v___x_689_, 1);
                    lean_ctor_set(v___x_689_, 0, v_a_678_);
                    v___x_693_ = v___x_689_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_678_);
                    v___x_693_ = v_reuseFailAlloc_704_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_694_ = lean_box(0);
                if v_isShared_681_ == 0 {
                    lean_ctor_set_tag(v___x_680_, 1);
                    lean_ctor_set(v___x_680_, 0, v_a_687_);
                    v___x_696_ = v___x_680_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_687_);
                    v___x_696_ = v_reuseFailAlloc_703_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_697_ = lean_unsigned_to_nat(3);
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
                v___x_712_ = lean_unsigned_to_nat(1);
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
                lean_dec_ref(v___x_714_);
                if lean_obj_tag(v___x_717_) == 0 {
                    v_a_718_ = lean_ctor_get(v___x_717_, 0);
                    v_isSharedCheck_736_ = (!lean_is_exclusive(v___x_717_)) as u8;
                    if v_isSharedCheck_736_ == 0 {
                        v___x_720_ = v___x_717_;
                        v_isShared_721_ = v_isSharedCheck_736_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_718_);
                        lean_dec(v___x_717_);
                        v___x_720_ = lean_box(0);
                        v_isShared_721_ = v_isSharedCheck_736_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_710_);
                    lean_dec(v_a_708_);
                    return v___x_717_;
                }
            }
            6 => {
                v___x_722_ = l_Lean_Meta_mkInstPiOfInstForall___closed__11;
                if v_isShared_721_ == 0 {
                    lean_ctor_set_tag(v___x_720_, 1);
                    lean_ctor_set(v___x_720_, 0, v_a_708_);
                    v___x_724_ = v___x_720_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_708_);
                    v___x_724_ = v_reuseFailAlloc_735_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_725_ = lean_box(0);
                if v_isShared_711_ == 0 {
                    lean_ctor_set_tag(v___x_710_, 1);
                    lean_ctor_set(v___x_710_, 0, v_a_718_);
                    v___x_727_ = v___x_710_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_718_);
                    v___x_727_ = v_reuseFailAlloc_734_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_728_ = lean_unsigned_to_nat(3);
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
    mut v_x_738_: *mut LeanObject,
    mut v_inst_739_: *mut LeanObject,
    mut v_a_740_: *mut LeanObject,
    mut v_a_741_: *mut LeanObject,
    mut v_a_742_: *mut LeanObject,
    mut v_a_743_: *mut LeanObject,
    mut v_a_744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_745_: *mut LeanObject = core::ptr::null_mut();
    v_res_745_ = l_Lean_Meta_mkInstPiOfInstForall(
        v_x_738_,
        v_inst_739_,
        v_a_740_,
        v_a_741_,
        v_a_742_,
        v_a_743_,
    );
    lean_dec(v_a_743_);
    lean_dec_ref(v_a_742_);
    lean_dec(v_a_741_);
    lean_dec_ref(v_a_740_);
    return v_res_745_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0(
    mut v_00_u03b1_746_: *mut LeanObject,
    mut v_msg_747_: *mut LeanObject,
    mut v___y_748_: *mut LeanObject,
    mut v___y_749_: *mut LeanObject,
    mut v___y_750_: *mut LeanObject,
    mut v___y_751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    v___x_753_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(
        v_msg_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_,
    );
    return v___x_753_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___boxed(
    mut v_00_u03b1_754_: *mut LeanObject,
    mut v_msg_755_: *mut LeanObject,
    mut v___y_756_: *mut LeanObject,
    mut v___y_757_: *mut LeanObject,
    mut v___y_758_: *mut LeanObject,
    mut v___y_759_: *mut LeanObject,
    mut v___y_760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_761_: *mut LeanObject = core::ptr::null_mut();
    v_res_761_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0(
        v_00_u03b1_754_,
        v_msg_755_,
        v___y_756_,
        v___y_757_,
        v___y_758_,
        v___y_759_,
    );
    lean_dec(v___y_759_);
    lean_dec_ref(v___y_758_);
    lean_dec(v___y_757_);
    lean_dec_ref(v___y_756_);
    return v_res_761_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkInstPiOfInstsForall_spec__0(
    mut v_as_762_: *mut LeanObject,
    mut v_sz_763_: usize,
    mut v_i_764_: usize,
    mut v_b_765_: *mut LeanObject,
    mut v___y_766_: *mut LeanObject,
    mut v___y_767_: *mut LeanObject,
    mut v___y_768_: *mut LeanObject,
    mut v___y_769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_771_: u8 = 0;
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: usize = 0;
    let mut v___x_777_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_771_ = lean_usize_dec_lt(v_i_764_, v_sz_763_);
                if v___x_771_ == 0 {
                    v___x_772_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_772_, 0, v_b_765_);
                    return v___x_772_;
                } else {
                    v_a_773_ = lean_array_uget_borrowed(v_as_762_, v_i_764_);
                    lean_inc(v_a_773_);
                    v___x_774_ = l_Lean_Meta_mkInstPiOfInstForall(
                        v_a_773_, v_b_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_,
                    );
                    if lean_obj_tag(v___x_774_) == 0 {
                        v_a_775_ = lean_ctor_get(v___x_774_, 0);
                        lean_inc(v_a_775_);
                        lean_dec_ref_known(v___x_774_, 1);
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
    mut v_as_779_: *mut LeanObject,
    mut v_sz_780_: *mut LeanObject,
    mut v_i_781_: *mut LeanObject,
    mut v_b_782_: *mut LeanObject,
    mut v___y_783_: *mut LeanObject,
    mut v___y_784_: *mut LeanObject,
    mut v___y_785_: *mut LeanObject,
    mut v___y_786_: *mut LeanObject,
    mut v___y_787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_788_: usize = 0;
    let mut v_i_boxed_789_: usize = 0;
    let mut v_res_790_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_788_ = lean_unbox_usize(v_sz_780_);
    lean_dec(v_sz_780_);
    v_i_boxed_789_ = lean_unbox_usize(v_i_781_);
    lean_dec(v_i_781_);
    v_res_790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkInstPiOfInstsForall_spec__0(v_as_779_, v_sz_boxed_788_, v_i_boxed_789_, v_b_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
    lean_dec(v___y_786_);
    lean_dec_ref(v___y_785_);
    lean_dec(v___y_784_);
    lean_dec_ref(v___y_783_);
    lean_dec_ref(v_as_779_);
    return v_res_790_;
}
pub unsafe fn l_Lean_Meta_mkInstPiOfInstsForall(
    mut v_xs_791_: *mut LeanObject,
    mut v_inst_792_: *mut LeanObject,
    mut v_a_793_: *mut LeanObject,
    mut v_a_794_: *mut LeanObject,
    mut v_a_795_: *mut LeanObject,
    mut v_a_796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_799_: usize = 0;
    let mut v___x_800_: usize = 0;
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    v___x_798_ = l_Array_reverse___redArg(v_xs_791_);
    v_sz_799_ = lean_array_size(v___x_798_);
    v___x_800_ = 0usize;
    v___x_801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkInstPiOfInstsForall_spec__0(v___x_798_, v_sz_799_, v___x_800_, v_inst_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_);
    lean_dec_ref(v___x_798_);
    return v___x_801_;
}
pub unsafe fn l_Lean_Meta_mkInstPiOfInstsForall___boxed(
    mut v_xs_802_: *mut LeanObject,
    mut v_inst_803_: *mut LeanObject,
    mut v_a_804_: *mut LeanObject,
    mut v_a_805_: *mut LeanObject,
    mut v_a_806_: *mut LeanObject,
    mut v_a_807_: *mut LeanObject,
    mut v_a_808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_809_: *mut LeanObject = core::ptr::null_mut();
    v_res_809_ = l_Lean_Meta_mkInstPiOfInstsForall(
        v_xs_802_,
        v_inst_803_,
        v_a_804_,
        v_a_805_,
        v_a_806_,
        v_a_807_,
    );
    lean_dec(v_a_807_);
    lean_dec_ref(v_a_806_);
    lean_dec(v_a_805_);
    lean_dec_ref(v_a_804_);
    return v_res_809_;
}
pub unsafe fn _init_l_Lean_Meta_mkFixOfMonFun___closed__1() -> *mut LeanObject {
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    v___x_811_ = l_Lean_Meta_mkFixOfMonFun___closed__0;
    v___x_812_ = l_Lean_stringToMessageData(v___x_811_);
    return v___x_812_;
}
pub unsafe fn l_Lean_Meta_mkFixOfMonFun(
    mut v_packedType_823_: *mut LeanObject,
    mut v_packedInst_824_: *mut LeanObject,
    mut v_hmono_825_: *mut LeanObject,
    mut v_a_826_: *mut LeanObject,
    mut v_a_827_: *mut LeanObject,
    mut v_a_828_: *mut LeanObject,
    mut v_a_829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_835_: u8 = 0;
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_837_: u8 = 0;
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_842_: u8 = 0;
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: u8 = 0;
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_865_: u8 = 0;
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_880_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_829_);
                lean_inc_ref(v_a_828_);
                lean_inc(v_a_827_);
                lean_inc_ref(v_a_826_);
                lean_inc_ref(v_packedInst_824_);
                v___x_831_ =
                    lean_infer_type(v_packedInst_824_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
                if lean_obj_tag(v___x_831_) == 0 {
                    v_a_832_ = lean_ctor_get(v___x_831_, 0);
                    v_isSharedCheck_880_ = (!lean_is_exclusive(v___x_831_)) as u8;
                    if v_isSharedCheck_880_ == 0 {
                        v___x_834_ = v___x_831_;
                        v_isShared_835_ = v_isSharedCheck_880_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_832_);
                        lean_dec(v___x_831_);
                        v___x_834_ = lean_box(0);
                        v_isShared_835_ = v_isSharedCheck_880_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_hmono_825_);
                    lean_dec_ref(v_packedInst_824_);
                    lean_dec_ref(v_packedType_823_);
                    return v___x_831_;
                }
            }
            1 => {
                v___x_836_ = l_Lean_Meta_mkInstPiOfInstForall___closed__3;
                v___x_837_ = l_Lean_Expr_isAppOf(v_a_832_, v___x_836_);
                lean_dec(v_a_832_);
                if v___x_837_ == 0 {
                    lean_inc(v_a_829_);
                    lean_inc_ref(v_a_828_);
                    lean_inc(v_a_827_);
                    lean_inc_ref(v_a_826_);
                    lean_inc_ref(v_packedInst_824_);
                    v___x_838_ =
                        lean_infer_type(v_packedInst_824_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
                    if lean_obj_tag(v___x_838_) == 0 {
                        v_a_839_ = lean_ctor_get(v___x_838_, 0);
                        v_isSharedCheck_865_ = (!lean_is_exclusive(v___x_838_)) as u8;
                        if v_isSharedCheck_865_ == 0 {
                            v___x_841_ = v___x_838_;
                            v_isShared_842_ = v_isSharedCheck_865_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_839_);
                            lean_dec(v___x_838_);
                            v___x_841_ = lean_box(0);
                            v_isShared_842_ = v_isSharedCheck_865_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_834_);
                        lean_dec_ref(v_hmono_825_);
                        lean_dec_ref(v_packedInst_824_);
                        lean_dec_ref(v_packedType_823_);
                        return v___x_838_;
                    }
                } else {
                    v___x_866_ = l_Lean_Meta_mkFixOfMonFun___closed__5;
                    if v_isShared_835_ == 0 {
                        lean_ctor_set_tag(v___x_834_, 1);
                        lean_ctor_set(v___x_834_, 0, v_packedType_823_);
                        v___x_868_ = v___x_834_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_879_, 0, v_packedType_823_);
                        v___x_868_ = v_reuseFailAlloc_879_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_843_ = l_Lean_Meta_mkInstPiOfInstForall___closed__5;
                v___x_844_ = l_Lean_Expr_isAppOf(v_a_839_, v___x_843_);
                lean_dec(v_a_839_);
                if v___x_844_ == 0 {
                    lean_del_object(v___x_841_);
                    lean_del_object(v___x_834_);
                    lean_dec_ref(v_hmono_825_);
                    lean_dec_ref(v_packedType_823_);
                    v___x_845_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkFixOfMonFun___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkFixOfMonFun___closed__1_once),
                        _init_l_Lean_Meta_mkFixOfMonFun___closed__1,
                    );
                    v___x_846_ = l_Lean_MessageData_ofExpr(v_packedInst_824_);
                    v___x_847_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_847_, 0, v___x_845_);
                    lean_ctor_set(v___x_847_, 1, v___x_846_);
                    v___x_848_ =
                        l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(
                            v___x_847_, v_a_826_, v_a_827_, v_a_828_, v_a_829_,
                        );
                    return v___x_848_;
                } else {
                    v___x_849_ = l_Lean_Meta_mkFixOfMonFun___closed__3;
                    if v_isShared_842_ == 0 {
                        lean_ctor_set_tag(v___x_841_, 1);
                        lean_ctor_set(v___x_841_, 0, v_packedType_823_);
                        v___x_851_ = v___x_841_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_864_, 0, v_packedType_823_);
                        v___x_851_ = v_reuseFailAlloc_864_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_835_ == 0 {
                    lean_ctor_set_tag(v___x_834_, 1);
                    lean_ctor_set(v___x_834_, 0, v_packedInst_824_);
                    v___x_853_ = v___x_834_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_863_, 0, v_packedInst_824_);
                    v___x_853_ = v_reuseFailAlloc_863_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_854_ = lean_box(0);
                v___x_855_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_855_, 0, v_hmono_825_);
                v___x_856_ = lean_unsigned_to_nat(4);
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
                v___x_869_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_869_, 0, v_packedInst_824_);
                v___x_870_ = lean_box(0);
                v___x_871_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_871_, 0, v_hmono_825_);
                v___x_872_ = lean_unsigned_to_nat(4);
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
    mut v_packedType_881_: *mut LeanObject,
    mut v_packedInst_882_: *mut LeanObject,
    mut v_hmono_883_: *mut LeanObject,
    mut v_a_884_: *mut LeanObject,
    mut v_a_885_: *mut LeanObject,
    mut v_a_886_: *mut LeanObject,
    mut v_a_887_: *mut LeanObject,
    mut v_a_888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_889_: *mut LeanObject = core::ptr::null_mut();
    v_res_889_ = l_Lean_Meta_mkFixOfMonFun(
        v_packedType_881_,
        v_packedInst_882_,
        v_hmono_883_,
        v_a_884_,
        v_a_885_,
        v_a_886_,
        v_a_887_,
    );
    lean_dec(v_a_887_);
    lean_dec_ref(v_a_886_);
    lean_dec(v_a_885_);
    lean_dec_ref(v_a_884_);
    return v_res_889_;
}
pub unsafe fn _init_l_Lean_Meta_toPartialOrder___closed__1() -> *mut LeanObject {
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    v___x_891_ = l_Lean_Meta_toPartialOrder___closed__0;
    v___x_892_ = l_Lean_stringToMessageData(v___x_891_);
    return v___x_892_;
}
pub unsafe fn l_Lean_Meta_toPartialOrder(
    mut v_packedInst_904_: *mut LeanObject,
    mut v_type_905_: *mut LeanObject,
    mut v_a_906_: *mut LeanObject,
    mut v_a_907_: *mut LeanObject,
    mut v_a_908_: *mut LeanObject,
    mut v_a_909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_915_: u8 = 0;
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: u8 = 0;
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_922_: u8 = 0;
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_924_: u8 = 0;
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_938_: u8 = 0;
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_948_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_909_);
                lean_inc_ref(v_a_908_);
                lean_inc(v_a_907_);
                lean_inc_ref(v_a_906_);
                lean_inc_ref(v_packedInst_904_);
                v___x_911_ =
                    lean_infer_type(v_packedInst_904_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
                if lean_obj_tag(v___x_911_) == 0 {
                    v_a_912_ = lean_ctor_get(v___x_911_, 0);
                    v_isSharedCheck_948_ = (!lean_is_exclusive(v___x_911_)) as u8;
                    if v_isSharedCheck_948_ == 0 {
                        v___x_914_ = v___x_911_;
                        v_isShared_915_ = v_isSharedCheck_948_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_912_);
                        lean_dec(v___x_911_);
                        v___x_914_ = lean_box(0);
                        v_isShared_915_ = v_isSharedCheck_948_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_type_905_);
                    lean_dec_ref(v_packedInst_904_);
                    return v___x_911_;
                }
            }
            1 => {
                v___x_916_ = l_Lean_Meta_mkInstPiOfInstForall___closed__3;
                v___x_917_ = l_Lean_Expr_isAppOf(v_a_912_, v___x_916_);
                lean_dec(v_a_912_);
                if v___x_917_ == 0 {
                    lean_del_object(v___x_914_);
                    lean_inc(v_a_909_);
                    lean_inc_ref(v_a_908_);
                    lean_inc(v_a_907_);
                    lean_inc_ref(v_a_906_);
                    lean_inc_ref(v_packedInst_904_);
                    v___x_918_ =
                        lean_infer_type(v_packedInst_904_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
                    if lean_obj_tag(v___x_918_) == 0 {
                        v_a_919_ = lean_ctor_get(v___x_918_, 0);
                        v_isSharedCheck_938_ = (!lean_is_exclusive(v___x_918_)) as u8;
                        if v_isSharedCheck_938_ == 0 {
                            v___x_921_ = v___x_918_;
                            v_isShared_922_ = v_isSharedCheck_938_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_919_);
                            lean_dec(v___x_918_);
                            v___x_921_ = lean_box(0);
                            v_isShared_922_ = v_isSharedCheck_938_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_type_905_);
                        lean_dec_ref(v_packedInst_904_);
                        return v___x_918_;
                    }
                } else {
                    v___x_939_ = l_Lean_Meta_toPartialOrder___closed__4;
                    if v_isShared_915_ == 0 {
                        lean_ctor_set_tag(v___x_914_, 1);
                        lean_ctor_set(v___x_914_, 0, v_packedInst_904_);
                        v___x_941_ = v___x_914_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_947_, 0, v_packedInst_904_);
                        v___x_941_ = v_reuseFailAlloc_947_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_923_ = l_Lean_Meta_mkInstPiOfInstForall___closed__5;
                v___x_924_ = l_Lean_Expr_isAppOf(v_a_919_, v___x_923_);
                lean_dec(v_a_919_);
                if v___x_924_ == 0 {
                    lean_del_object(v___x_921_);
                    lean_dec(v_type_905_);
                    v___x_925_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_toPartialOrder___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_toPartialOrder___closed__1_once),
                        _init_l_Lean_Meta_toPartialOrder___closed__1,
                    );
                    v___x_926_ = l_Lean_MessageData_ofExpr(v_packedInst_904_);
                    v___x_927_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_927_, 0, v___x_925_);
                    lean_ctor_set(v___x_927_, 1, v___x_926_);
                    v___x_928_ =
                        l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(
                            v___x_927_, v_a_906_, v_a_907_, v_a_908_, v_a_909_,
                        );
                    return v___x_928_;
                } else {
                    v___x_929_ = l_Lean_Meta_toPartialOrder___closed__3;
                    if v_isShared_922_ == 0 {
                        lean_ctor_set_tag(v___x_921_, 1);
                        lean_ctor_set(v___x_921_, 0, v_packedInst_904_);
                        v___x_931_ = v___x_921_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_937_, 0, v_packedInst_904_);
                        v___x_931_ = v_reuseFailAlloc_937_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_932_ = lean_unsigned_to_nat(2);
                v___x_933_ = lean_mk_empty_array_with_capacity(v___x_932_);
                v___x_934_ = lean_array_push(v___x_933_, v_type_905_);
                v___x_935_ = lean_array_push(v___x_934_, v___x_931_);
                v___x_936_ = l_Lean_Meta_mkAppOptM(
                    v___x_929_, v___x_935_, v_a_906_, v_a_907_, v_a_908_, v_a_909_,
                );
                return v___x_936_;
            }
            4 => {
                v___x_942_ = lean_unsigned_to_nat(2);
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
    mut v_packedInst_949_: *mut LeanObject,
    mut v_type_950_: *mut LeanObject,
    mut v_a_951_: *mut LeanObject,
    mut v_a_952_: *mut LeanObject,
    mut v_a_953_: *mut LeanObject,
    mut v_a_954_: *mut LeanObject,
    mut v_a_955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_956_: *mut LeanObject = core::ptr::null_mut();
    v_res_956_ = l_Lean_Meta_toPartialOrder(
        v_packedInst_949_,
        v_type_950_,
        v_a_951_,
        v_a_952_,
        v_a_953_,
        v_a_954_,
    );
    lean_dec(v_a_954_);
    lean_dec_ref(v_a_953_);
    lean_dec(v_a_952_);
    lean_dec_ref(v_a_951_);
    return v_res_956_;
}
pub unsafe fn _init_l_Lean_Meta_mkInstCCPOPProd___closed__2() -> *mut LeanObject {
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    v___x_962_ = lean_box(0);
    v___x_963_ = lean_unsigned_to_nat(4);
    v___x_964_ = lean_mk_empty_array_with_capacity(v___x_963_);
    v___x_965_ = lean_array_push(v___x_964_, v___x_962_);
    return v___x_965_;
}
pub unsafe fn _init_l_Lean_Meta_mkInstCCPOPProd___closed__3() -> *mut LeanObject {
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    v___x_966_ = lean_box(0);
    v___x_967_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkInstCCPOPProd___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkInstCCPOPProd___closed__2_once),
        _init_l_Lean_Meta_mkInstCCPOPProd___closed__2,
    );
    v___x_968_ = lean_array_push(v___x_967_, v___x_966_);
    return v___x_968_;
}
pub unsafe fn l_Lean_Meta_mkInstCCPOPProd(
    mut v_inst_u2081_969_: *mut LeanObject,
    mut v_inst_u2082_970_: *mut LeanObject,
    mut v_a_971_: *mut LeanObject,
    mut v_a_972_: *mut LeanObject,
    mut v_a_973_: *mut LeanObject,
    mut v_a_974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    v___x_976_ = l_Lean_Meta_mkInstCCPOPProd___closed__1;
    v___x_977_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_977_, 0, v_inst_u2081_969_);
    v___x_978_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_978_, 0, v_inst_u2082_970_);
    v___x_979_ = lean_obj_once(
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
    mut v_inst_u2081_983_: *mut LeanObject,
    mut v_inst_u2082_984_: *mut LeanObject,
    mut v_a_985_: *mut LeanObject,
    mut v_a_986_: *mut LeanObject,
    mut v_a_987_: *mut LeanObject,
    mut v_a_988_: *mut LeanObject,
    mut v_a_989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_990_: *mut LeanObject = core::ptr::null_mut();
    v_res_990_ = l_Lean_Meta_mkInstCCPOPProd(
        v_inst_u2081_983_,
        v_inst_u2082_984_,
        v_a_985_,
        v_a_986_,
        v_a_987_,
        v_a_988_,
    );
    lean_dec(v_a_988_);
    lean_dec_ref(v_a_987_);
    lean_dec(v_a_986_);
    lean_dec_ref(v_a_985_);
    return v_res_990_;
}
pub unsafe fn l_Lean_Meta_mkInstCompleteLatticePProd(
    mut v_inst_u2081_996_: *mut LeanObject,
    mut v_inst_u2082_997_: *mut LeanObject,
    mut v_a_998_: *mut LeanObject,
    mut v_a_999_: *mut LeanObject,
    mut v_a_1000_: *mut LeanObject,
    mut v_a_1001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    v___x_1003_ = l_Lean_Meta_mkInstCompleteLatticePProd___closed__1;
    v___x_1004_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1004_, 0, v_inst_u2081_996_);
    v___x_1005_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1005_, 0, v_inst_u2082_997_);
    v___x_1006_ = lean_obj_once(
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
    mut v_inst_u2081_1010_: *mut LeanObject,
    mut v_inst_u2082_1011_: *mut LeanObject,
    mut v_a_1012_: *mut LeanObject,
    mut v_a_1013_: *mut LeanObject,
    mut v_a_1014_: *mut LeanObject,
    mut v_a_1015_: *mut LeanObject,
    mut v_a_1016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1017_: *mut LeanObject = core::ptr::null_mut();
    v_res_1017_ = l_Lean_Meta_mkInstCompleteLatticePProd(
        v_inst_u2081_1010_,
        v_inst_u2082_1011_,
        v_a_1012_,
        v_a_1013_,
        v_a_1014_,
        v_a_1015_,
    );
    lean_dec(v_a_1015_);
    lean_dec_ref(v_a_1014_);
    lean_dec(v_a_1013_);
    lean_dec_ref(v_a_1012_);
    return v_res_1017_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_mkPackedPPRodInstance_spec__3(
    mut v_a_1018_: *mut LeanObject,
    mut v_a_1019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1025_: u8 = 0;
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1031_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1018_) == 0 {
                    v___x_1020_ = l_List_reverse___redArg(v_a_1019_);
                    return v___x_1020_;
                } else {
                    v_head_1021_ = lean_ctor_get(v_a_1018_, 0);
                    v_tail_1022_ = lean_ctor_get(v_a_1018_, 1);
                    v_isSharedCheck_1031_ = (!lean_is_exclusive(v_a_1018_)) as u8;
                    if v_isSharedCheck_1031_ == 0 {
                        v___x_1024_ = v_a_1018_;
                        v_isShared_1025_ = v_isSharedCheck_1031_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1022_);
                        lean_inc(v_head_1021_);
                        lean_dec(v_a_1018_);
                        v___x_1024_ = lean_box(0);
                        v_isShared_1025_ = v_isSharedCheck_1031_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1026_ = l_Lean_MessageData_ofExpr(v_head_1021_);
                if v_isShared_1025_ == 0 {
                    lean_ctor_set(v___x_1024_, 1, v_a_1019_);
                    lean_ctor_set(v___x_1024_, 0, v___x_1026_);
                    v___x_1028_ = v___x_1024_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1026_);
                    lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_a_1019_);
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
    mut v_bs_1034_: *mut LeanObject,
    mut v___y_1035_: *mut LeanObject,
    mut v___y_1036_: *mut LeanObject,
    mut v___y_1037_: *mut LeanObject,
    mut v___y_1038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1040_: u8 = 0;
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: usize = 0;
    let mut v___x_1048_: usize = 0;
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1054_: u8 = 0;
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1058_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1040_ = lean_usize_dec_lt(v_i_1033_, v_sz_1032_);
                if v___x_1040_ == 0 {
                    v___x_1041_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1041_, 0, v_bs_1034_);
                    return v___x_1041_;
                } else {
                    v_v_1042_ = lean_array_uget_borrowed(v_bs_1034_, v_i_1033_);
                    lean_inc(v___y_1038_);
                    lean_inc_ref(v___y_1037_);
                    lean_inc(v___y_1036_);
                    lean_inc_ref(v___y_1035_);
                    lean_inc(v_v_1042_);
                    v___x_1043_ = lean_infer_type(
                        v_v_1042_,
                        v___y_1035_,
                        v___y_1036_,
                        v___y_1037_,
                        v___y_1038_,
                    );
                    if lean_obj_tag(v___x_1043_) == 0 {
                        v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
                        lean_inc(v_a_1044_);
                        lean_dec_ref_known(v___x_1043_, 1);
                        v___x_1045_ = lean_unsigned_to_nat(0);
                        v_bs_x27_1046_ = lean_array_uset(v_bs_1034_, v_i_1033_, v___x_1045_);
                        v___x_1047_ = 1usize;
                        v___x_1048_ = lean_usize_add(v_i_1033_, v___x_1047_);
                        v___x_1049_ = lean_array_uset(v_bs_x27_1046_, v_i_1033_, v_a_1044_);
                        v_i_1033_ = v___x_1048_;
                        v_bs_1034_ = v___x_1049_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_1034_);
                        v_a_1051_ = lean_ctor_get(v___x_1043_, 0);
                        v_isSharedCheck_1058_ = (!lean_is_exclusive(v___x_1043_)) as u8;
                        if v_isSharedCheck_1058_ == 0 {
                            v___x_1053_ = v___x_1043_;
                            v_isShared_1054_ = v_isSharedCheck_1058_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1051_);
                            lean_dec(v___x_1043_);
                            v___x_1053_ = lean_box(0);
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
                    v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
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
    mut v_sz_1059_: *mut LeanObject,
    mut v_i_1060_: *mut LeanObject,
    mut v_bs_1061_: *mut LeanObject,
    mut v___y_1062_: *mut LeanObject,
    mut v___y_1063_: *mut LeanObject,
    mut v___y_1064_: *mut LeanObject,
    mut v___y_1065_: *mut LeanObject,
    mut v___y_1066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1067_: usize = 0;
    let mut v_i_boxed_1068_: usize = 0;
    let mut v_res_1069_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1067_ = lean_unbox_usize(v_sz_1059_);
    lean_dec(v_sz_1059_);
    v_i_boxed_1068_ = lean_unbox_usize(v_i_1060_);
    lean_dec(v_i_1060_);
    v_res_1069_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkPackedPPRodInstance_spec__0(v_sz_boxed_1067_, v_i_boxed_1068_, v_bs_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
    lean_dec(v___y_1065_);
    lean_dec_ref(v___y_1064_);
    lean_dec(v___y_1063_);
    lean_dec_ref(v___y_1062_);
    return v_res_1069_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__1(
    mut v_as_1070_: *mut LeanObject,
    mut v_i_1071_: usize,
    mut v_stop_1072_: usize,
) -> u8 {
    let mut v___x_1073_: u8 = 0;
    let mut v___x_1074_: u8 = 0;
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_as_1082_: *mut LeanObject,
    mut v_i_1083_: *mut LeanObject,
    mut v_stop_1084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1085_: usize = 0;
    let mut v_stop_boxed_1086_: usize = 0;
    let mut v_res_1087_: u8 = 0;
    let mut v_r_1088_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1085_ = lean_unbox_usize(v_i_1083_);
    lean_dec(v_i_1083_);
    v_stop_boxed_1086_ = lean_unbox_usize(v_stop_1084_);
    lean_dec(v_stop_1084_);
    v_res_1087_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__1(v_as_1082_, v_i_boxed_1085_, v_stop_boxed_1086_);
    lean_dec_ref(v_as_1082_);
    v_r_1088_ = lean_box((v_res_1087_) as usize);
    return v_r_1088_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__2(
    mut v___x_1089_: u8,
    mut v_as_1090_: *mut LeanObject,
    mut v_i_1091_: usize,
    mut v_stop_1092_: usize,
) -> u8 {
    let mut v___x_1094_: usize = 0;
    let mut v___x_1095_: usize = 0;
    let mut v___x_1097_: u8 = 0;
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___x_1102_: *mut LeanObject,
    mut v_as_1103_: *mut LeanObject,
    mut v_i_1104_: *mut LeanObject,
    mut v_stop_1105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1493__boxed_1106_: u8 = 0;
    let mut v_i_boxed_1107_: usize = 0;
    let mut v_stop_boxed_1108_: usize = 0;
    let mut v_res_1109_: u8 = 0;
    let mut v_r_1110_: *mut LeanObject = core::ptr::null_mut();
    v___x_1493__boxed_1106_ = (lean_unbox(v___x_1102_) as u8);
    v_i_boxed_1107_ = lean_unbox_usize(v_i_1104_);
    lean_dec(v_i_1104_);
    v_stop_boxed_1108_ = lean_unbox_usize(v_stop_1105_);
    lean_dec(v_stop_1105_);
    v_res_1109_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__2(v___x_1493__boxed_1106_, v_as_1103_, v_i_boxed_1107_, v_stop_boxed_1108_);
    lean_dec_ref(v_as_1103_);
    v_r_1110_ = lean_box((v_res_1109_) as usize);
    return v_r_1110_;
}
pub unsafe fn _init_l_Lean_Meta_mkPackedPPRodInstance___closed__3() -> *mut LeanObject {
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    v___x_1114_ = l_Lean_Meta_mkPackedPPRodInstance___closed__2;
    v___x_1115_ = l_Lean_stringToMessageData(v___x_1114_);
    return v___x_1115_;
}
pub unsafe fn _init_l_Lean_Meta_mkPackedPPRodInstance___closed__5() -> *mut LeanObject {
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    v___x_1117_ = l_Lean_Meta_mkPackedPPRodInstance___closed__4;
    v___x_1118_ = l_Lean_stringToMessageData(v___x_1117_);
    return v___x_1118_;
}
pub unsafe fn l_Lean_Meta_mkPackedPPRodInstance(
    mut v_insts_1119_: *mut LeanObject,
    mut v_a_1120_: *mut LeanObject,
    mut v_a_1121_: *mut LeanObject,
    mut v_a_1122_: *mut LeanObject,
    mut v_a_1123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_1125_: usize = 0;
    let mut v___x_1126_: usize = 0;
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: u8 = 0;
    let mut v___x_1140_: usize = 0;
    let mut v___x_1141_: u8 = 0;
    let mut v___x_1142_: u8 = 0;
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1159_: u8 = 0;
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1163_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_1125_ = lean_array_size(v_insts_1119_);
                v___x_1126_ = 0usize;
                lean_inc_ref(v_insts_1119_);
                v___x_1127_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkPackedPPRodInstance_spec__0(v_sz_1125_, v___x_1126_, v_insts_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
                if lean_obj_tag(v___x_1127_) == 0 {
                    v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
                    lean_inc(v_a_1128_);
                    lean_dec_ref_known(v___x_1127_, 1);
                    v___x_1137_ = lean_unsigned_to_nat(0);
                    v___x_1138_ = lean_array_get_size(v_a_1128_);
                    v___x_1139_ = lean_nat_dec_lt(v___x_1137_, v___x_1138_);
                    if v___x_1139_ == 0 {
                        lean_dec(v_a_1128_);
                        state = 2;
                        continue;
                    } else {
                        if v___x_1139_ == 0 {
                            lean_dec(v_a_1128_);
                            state = 2;
                            continue;
                        } else {
                            v___x_1140_ = lean_usize_of_nat(v___x_1138_);
                            v___x_1141_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__1(v_a_1128_, v___x_1126_, v___x_1140_);
                            if v___x_1141_ == 0 {
                                lean_dec(v_a_1128_);
                                state = 2;
                                continue;
                            } else {
                                if v___x_1139_ == 0 {
                                    lean_dec(v_a_1128_);
                                    state = 1;
                                    continue;
                                } else {
                                    if v___x_1139_ == 0 {
                                        lean_dec(v_a_1128_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_1142_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkPackedPPRodInstance_spec__2(v___x_1141_, v_a_1128_, v___x_1126_, v___x_1140_);
                                        if v___x_1142_ == 0 {
                                            lean_dec(v_a_1128_);
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_1143_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_mkPackedPPRodInstance___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_mkPackedPPRodInstance___closed__3_once), _init_l_Lean_Meta_mkPackedPPRodInstance___closed__3);
                                            v___x_1144_ = lean_array_to_list(v_a_1128_);
                                            v___x_1145_ = lean_box(0);
                                            v___x_1146_ = l_List_mapTR_loop___at___00Lean_Meta_mkPackedPPRodInstance_spec__3(v___x_1144_, v___x_1145_);
                                            v___x_1147_ = l_Lean_MessageData_ofList(v___x_1146_);
                                            v___x_1148_ = lean_alloc_ctor(7, 2, (0) as u32);
                                            lean_ctor_set(v___x_1148_, 0, v___x_1143_);
                                            lean_ctor_set(v___x_1148_, 1, v___x_1147_);
                                            v___x_1149_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_mkPackedPPRodInstance___closed__5), core::ptr::addr_of_mut!(l_Lean_Meta_mkPackedPPRodInstance___closed__5_once), _init_l_Lean_Meta_mkPackedPPRodInstance___closed__5);
                                            v___x_1150_ = lean_alloc_ctor(7, 2, (0) as u32);
                                            lean_ctor_set(v___x_1150_, 0, v___x_1148_);
                                            lean_ctor_set(v___x_1150_, 1, v___x_1149_);
                                            v___x_1151_ = lean_array_to_list(v_insts_1119_);
                                            v___x_1152_ = l_List_mapTR_loop___at___00Lean_Meta_mkPackedPPRodInstance_spec__3(v___x_1151_, v___x_1145_);
                                            v___x_1153_ = l_Lean_MessageData_ofList(v___x_1152_);
                                            v___x_1154_ = lean_alloc_ctor(7, 2, (0) as u32);
                                            lean_ctor_set(v___x_1154_, 0, v___x_1150_);
                                            lean_ctor_set(v___x_1154_, 1, v___x_1153_);
                                            v___x_1155_ = l_Lean_throwError___at___00Lean_Meta_mkInstPiOfInstForall_spec__0___redArg(v___x_1154_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
                                            return v___x_1155_;
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_insts_1119_);
                    v_a_1156_ = lean_ctor_get(v___x_1127_, 0);
                    v_isSharedCheck_1163_ = (!lean_is_exclusive(v___x_1127_)) as u8;
                    if v_isSharedCheck_1163_ == 0 {
                        v___x_1158_ = v___x_1127_;
                        v_isShared_1159_ = v_isSharedCheck_1163_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1156_);
                        lean_dec(v___x_1127_);
                        v___x_1158_ = lean_box(0);
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
                    v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
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
    mut v_insts_1164_: *mut LeanObject,
    mut v_a_1165_: *mut LeanObject,
    mut v_a_1166_: *mut LeanObject,
    mut v_a_1167_: *mut LeanObject,
    mut v_a_1168_: *mut LeanObject,
    mut v_a_1169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1170_: *mut LeanObject = core::ptr::null_mut();
    v_res_1170_ = l_Lean_Meta_mkPackedPPRodInstance(
        v_insts_1164_,
        v_a_1165_,
        v_a_1166_,
        v_a_1167_,
        v_a_1168_,
    );
    lean_dec(v_a_1168_);
    lean_dec_ref(v_a_1167_);
    lean_dec(v_a_1166_);
    lean_dec_ref(v_a_1165_);
    return v_res_1170_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Order(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_PProdN(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Internal_Order_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Order(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Order(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_PProdN(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Internal_Order_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Order(builtin);
}
