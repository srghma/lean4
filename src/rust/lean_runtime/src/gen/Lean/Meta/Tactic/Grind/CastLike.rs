// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.CastLike
// Imports: Lean.Expr Init.Grind.Ring.Envelope Init.Grind.Module.Envelope
use crate::r#gen::Init::Grind::Module::Envelope::{
    initialize_Init_Grind_Module_Envelope, runtime_initialize_Init_Grind_Module_Envelope,
};
use crate::r#gen::Init::Grind::Ring::Envelope::{
    initialize_Init_Grind_Ring_Envelope, runtime_initialize_Init_Grind_Ring_Envelope,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5};
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Expr_getAppFn, runtime_initialize_Lean_Expr,
};
use crate::lean_imports_rs::Init::Prelude::lean_name_eq;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub static l_Lean_Meta_Grind_isCastLikeDeclName___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Meta_Grind_isCastLikeDeclName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_isCastLikeDeclName___closed__1_value: LeanStringObject<6> =
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
        m_data: [71, 114, 105, 110, 100, 0],
    };
static mut l_Lean_Meta_Grind_isCastLikeDeclName___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_isCastLikeDeclName___closed__2_value: LeanStringObject<6> =
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
        m_data: [84, 111, 73, 110, 116, 0],
    };
static mut l_Lean_Meta_Grind_isCastLikeDeclName___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_isCastLikeDeclName___closed__3_value: LeanStringObject<6> =
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
        m_data: [116, 111, 73, 110, 116, 0],
    };
static mut l_Lean_Meta_Grind_isCastLikeDeclName___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__3_value) as *mut LeanObject;
static l_Lean_Meta_Grind_isCastLikeDeclName___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_isCastLikeDeclName___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__1_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_isCastLikeDeclName___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__2_value)
                as *mut LeanObject,
            16822059798527729847 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_isCastLikeDeclName___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__3_value)
                as *mut LeanObject,
            2495166364501146107 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_isCastLikeDeclName___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_isCastLikeDeclName___closed__5_value: LeanStringObject<8> =
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
        m_data: [78, 97, 116, 67, 97, 115, 116, 0],
    };
static mut l_Lean_Meta_Grind_isCastLikeDeclName___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__5_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_isCastLikeDeclName___closed__6_value: LeanStringObject<8> =
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
        m_data: [110, 97, 116, 67, 97, 115, 116, 0],
    };
static mut l_Lean_Meta_Grind_isCastLikeDeclName___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__6_value) as *mut LeanObject;
static l_Lean_Meta_Grind_isCastLikeDeclName___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__5_value)
                as *mut LeanObject,
            5779414593499529281 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_isCastLikeDeclName___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__6_value)
                as *mut LeanObject,
            7063772860359172143 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_isCastLikeDeclName___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__7_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_isCastLikeDeclName___closed__8_value: LeanStringObject<8> =
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
        m_data: [73, 110, 116, 67, 97, 115, 116, 0],
    };
static mut l_Lean_Meta_Grind_isCastLikeDeclName___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__8_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_isCastLikeDeclName___closed__9_value: LeanStringObject<8> =
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
        m_data: [105, 110, 116, 67, 97, 115, 116, 0],
    };
static mut l_Lean_Meta_Grind_isCastLikeDeclName___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__9_value) as *mut LeanObject;
static l_Lean_Meta_Grind_isCastLikeDeclName___closed__10_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__8_value)
                as *mut LeanObject,
            4977321555018234431 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_isCastLikeDeclName___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__10_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__9_value)
                as *mut LeanObject,
            4463466624472370110 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_isCastLikeDeclName___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__10_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_isCastLikeDeclName___closed__11_value: LeanStringObject<5> =
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
        m_data: [82, 105, 110, 103, 0],
    };
static mut l_Lean_Meta_Grind_isCastLikeDeclName___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__11_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_isCastLikeDeclName___closed__12_value: LeanStringObject<11> =
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
        m_data: [79, 102, 83, 101, 109, 105, 114, 105, 110, 103, 0],
    };
static mut l_Lean_Meta_Grind_isCastLikeDeclName___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__12_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_isCastLikeDeclName___closed__13_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [116, 111, 81, 0],
    };
static mut l_Lean_Meta_Grind_isCastLikeDeclName___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__13_value) as *mut LeanObject;
static l_Lean_Meta_Grind_isCastLikeDeclName___closed__14_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_isCastLikeDeclName___closed__14_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__14_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__1_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_isCastLikeDeclName___closed__14_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__14_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__11_value)
                as *mut LeanObject,
            10806710915646349764 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_isCastLikeDeclName___closed__14_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__14_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__12_value)
                as *mut LeanObject,
            8254287559757149654 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_isCastLikeDeclName___closed__14_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__14_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__13_value)
                as *mut LeanObject,
            5073726620895580904 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_isCastLikeDeclName___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__14_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_isCastLikeDeclName___closed__15_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [73, 110, 116, 77, 111, 100, 117, 108, 101, 0],
    };
static mut l_Lean_Meta_Grind_isCastLikeDeclName___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__15_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_isCastLikeDeclName___closed__16_value: LeanStringObject<12> =
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
        m_data: [79, 102, 78, 97, 116, 77, 111, 100, 117, 108, 101, 0],
    };
static mut l_Lean_Meta_Grind_isCastLikeDeclName___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__16_value) as *mut LeanObject;
static l_Lean_Meta_Grind_isCastLikeDeclName___closed__17_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_isCastLikeDeclName___closed__17_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__17_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__1_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_isCastLikeDeclName___closed__17_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__17_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__15_value)
                as *mut LeanObject,
            7605204649477761179 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_isCastLikeDeclName___closed__17_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__17_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__16_value)
                as *mut LeanObject,
            11314908490917688650 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_isCastLikeDeclName___closed__17_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__17_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__13_value)
                as *mut LeanObject,
            6592053806809043044 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_isCastLikeDeclName___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isCastLikeDeclName___closed__17_value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Grind_isCastLikeDeclName(mut v_declName_102_: *mut LeanObject) -> u8 {
    let mut v___y_104_: u8 = 0;
    let mut v___x_105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_106_: u8 = 0;
    let mut v___x_107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_108_: u8 = 0;
    let mut v___x_109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_110_: u8 = 0;
    let mut v___x_111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_112_: u8 = 0;
    let mut v___x_113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_111_ = l_Lean_Meta_Grind_isCastLikeDeclName___closed__14;
                v___x_112_ = lean_name_eq(v_declName_102_, v___x_111_);
                if v___x_112_ == 0 {
                    v___x_113_ = l_Lean_Meta_Grind_isCastLikeDeclName___closed__17;
                    v___x_114_ = lean_name_eq(v_declName_102_, v___x_113_);
                    v___y_104_ = v___x_114_;
                    state = 1;
                    continue;
                } else {
                    v___y_104_ = v___x_112_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_104_ == 0 {
                    v___x_105_ = l_Lean_Meta_Grind_isCastLikeDeclName___closed__4;
                    v___x_106_ = lean_name_eq(v_declName_102_, v___x_105_);
                    if v___x_106_ == 0 {
                        v___x_107_ = l_Lean_Meta_Grind_isCastLikeDeclName___closed__7;
                        v___x_108_ = lean_name_eq(v_declName_102_, v___x_107_);
                        if v___x_108_ == 0 {
                            v___x_109_ = l_Lean_Meta_Grind_isCastLikeDeclName___closed__10;
                            v___x_110_ = lean_name_eq(v_declName_102_, v___x_109_);
                            return v___x_110_;
                        } else {
                            return v___x_108_;
                        }
                    } else {
                        return v___x_106_;
                    }
                } else {
                    return v___y_104_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_isCastLikeDeclName___boxed(
    mut v_declName_115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_116_: u8 = 0;
    let mut v_r_117_: *mut LeanObject = core::ptr::null_mut();
    v_res_116_ = l_Lean_Meta_Grind_isCastLikeDeclName(v_declName_115_);
    lean_dec(v_declName_115_);
    v_r_117_ = lean_box((v_res_116_) as usize);
    return v_r_117_;
}
pub unsafe fn l_Lean_Meta_Grind_isCastLikeFn(mut v_f_118_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_f_118_) == 4 {
        let mut v_declName_119_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_120_: u8 = 0;
        v_declName_119_ = lean_ctor_get(v_f_118_, 0);
        v___x_120_ = l_Lean_Meta_Grind_isCastLikeDeclName(v_declName_119_);
        return v___x_120_;
    } else {
        let mut v___x_121_: u8 = 0;
        v___x_121_ = 0;
        return v___x_121_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_isCastLikeFn___boxed(
    mut v_f_122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_123_: u8 = 0;
    let mut v_r_124_: *mut LeanObject = core::ptr::null_mut();
    v_res_123_ = l_Lean_Meta_Grind_isCastLikeFn(v_f_122_);
    lean_dec_ref(v_f_122_);
    v_r_124_ = lean_box((v_res_123_) as usize);
    return v_r_124_;
}
pub unsafe fn l_Lean_Meta_Grind_isCastLikeApp(mut v_e_125_: *mut LeanObject) -> u8 {
    let mut v___x_126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_127_: u8 = 0;
    v___x_126_ = l_Lean_Expr_getAppFn(v_e_125_);
    v___x_127_ = l_Lean_Meta_Grind_isCastLikeFn(v___x_126_);
    lean_dec_ref(v___x_126_);
    return v___x_127_;
}
pub unsafe fn l_Lean_Meta_Grind_isCastLikeApp___boxed(
    mut v_e_128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_129_: u8 = 0;
    let mut v_r_130_: *mut LeanObject = core::ptr::null_mut();
    v_res_129_ = l_Lean_Meta_Grind_isCastLikeApp(v_e_128_);
    lean_dec_ref(v_e_128_);
    v_r_130_ = lean_box((v_res_129_) as usize);
    return v_r_130_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_CastLike(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_Envelope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Module_Envelope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_CastLike(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_CastLike(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Ring_Envelope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Module_Envelope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_CastLike(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_CastLike(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_CastLike(builtin);
}
