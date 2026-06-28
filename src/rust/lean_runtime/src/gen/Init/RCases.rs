// Lean compiler output
// Module: Init.RCases
// Imports: Init.Meta
use crate::r#gen::Init::Meta::{initialize_Init_Meta, runtime_initialize_Init_Meta};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5,
};
use crate::r#gen::Init::Tactics::l_Lean_Parser_Tactic_elimTarget;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_ctor_set_uint8,
    lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent,
    lean_obj_once, lean_unsigned_to_nat,
};
pub static l_Lean_Parser_Tactic_rcasesPat_quot___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Parser_Tactic_rcasesPat_quot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_quot___closed__1_value: LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_quot___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_quot___closed__2_value: LeanStringObject<5> =
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
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_quot___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_quot___closed__3_value: LeanStringObject<5> =
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
        m_data: [113, 117, 111, 116, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_quot___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__3_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_rcasesPat_quot___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPat_quot___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPat_quot___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__2_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_rcasesPat_quot___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__3_value)
                as *mut LeanObject,
            5855146430765573009 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_quot___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_quot___closed__5_value: LeanStringObject<10> =
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
        m_data: [114, 99, 97, 115, 101, 115, 80, 97, 116, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_quot___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__5_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_rcasesPat_quot___closed__6_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__5_value)
                as *mut LeanObject,
            13727717468381035411 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_rcasesPat_quot___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__6_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__3_value)
                as *mut LeanObject,
            10558651730561063673 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_quot___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_quot___closed__7_value: LeanStringObject<8> =
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
        m_data: [97, 110, 100, 116, 104, 101, 110, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_quot___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__7_value)
                as *mut LeanObject,
            12571085391447129896 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_quot___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_quot___closed__9_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [96, 40, 114, 99, 97, 115, 101, 115, 80, 97, 116, 124, 32, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_quot___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_quot___closed__10_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_quot___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_quot___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__5_value)
                as *mut LeanObject,
            13727717468381035411 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_quot___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_quot___closed__12_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__11_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_quot___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_quot___closed__13_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [41, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_quot___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__13_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_quot___closed__14_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_quot___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__14_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_quot___closed__15_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_quot___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__15_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_quot___closed__16_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_quot___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__16_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_quot___closed__17_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__6_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__16_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_quot___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__17_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_quot___closed__18_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__4_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_quot___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__18_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_rcasesPat_quot: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__18_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Category_rcasesPat: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_rcasesPatMed___closed__0_value: LeanStringObject<13> =
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
        m_data: [114, 99, 97, 115, 101, 115, 80, 97, 116, 77, 101, 100, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPatMed___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPatMed___closed__1_value: LeanStringObject<7> =
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
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPatMed___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__1_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_rcasesPatMed___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPatMed___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPatMed___closed__2_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_rcasesPatMed___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__2_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__0_value)
                as *mut LeanObject,
            10749841504898977277 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPatMed___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPatMed___closed__3_value: LeanStringObject<4> =
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
        m_data: [32, 124, 32, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPatMed___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPatMed___closed__4_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPatMed___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPatMed___closed__5_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 11,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__4_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPatMed___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPatMed___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPatMed___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_rcasesPatMed: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPatLo___closed__0_value: LeanStringObject<12> =
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
        m_data: [114, 99, 97, 115, 101, 115, 80, 97, 116, 76, 111, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPatLo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_rcasesPatLo___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPatLo___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPatLo___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_rcasesPatLo___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__0_value) as *mut LeanObject,
        15468277551544524421 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_rcasesPatLo___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPatLo___closed__2_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [111, 112, 116, 105, 111, 110, 97, 108, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPatLo___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPatLo___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__2_value) as *mut LeanObject,
        18170484695678750185 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_rcasesPatLo___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPatLo___closed__4_value: LeanStringObject<4> =
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
        m_data: [32, 58, 32, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPatLo___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPatLo___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_rcasesPatLo___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPatLo___closed__6_value: LeanStringObject<5> =
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
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPatLo___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPatLo___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__6_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_rcasesPatLo___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPatLo___closed__8_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__7_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_rcasesPatLo___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPatLo___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_rcasesPatLo___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPatLo___closed__10_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPatLo___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPatLo___closed__11_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPatLo___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPatLo___closed__12_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPatLo___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__12_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_rcasesPatLo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_one___closed__0_value: LeanStringObject<4> =
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
        m_data: [111, 110, 101, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_one___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_one___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_rcasesPat_one___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPat_one___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_one___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPat_one___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_one___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPat_one___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_one___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__5_value)
                as *mut LeanObject,
            1416858759244133794 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_rcasesPat_one___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_one___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_one___closed__0_value)
                as *mut LeanObject,
            12149849828610578618 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_one___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_one___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_one___closed__2_value: LeanStringObject<6> =
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
        m_data: [105, 100, 101, 110, 116, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_one___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_one___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_one___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_one___closed__2_value)
                as *mut LeanObject,
            5117844058249666356 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_one___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_one___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_one___closed__4_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_one___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_one___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_one___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_one___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_one___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_one___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_one___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_one___closed__5_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_rcasesPat_one: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_one___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_ignore___closed__0_value: LeanStringObject<7> =
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
        m_data: [105, 103, 110, 111, 114, 101, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_ignore___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_ignore___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_rcasesPat_ignore___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPat_ignore___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_ignore___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPat_ignore___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_ignore___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPat_ignore___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_ignore___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__5_value)
                as *mut LeanObject,
            1416858759244133794 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_rcasesPat_ignore___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_ignore___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_ignore___closed__0_value)
                as *mut LeanObject,
            1909600920881732003 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_ignore___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_ignore___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_ignore___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [95, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_ignore___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_ignore___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_ignore___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_ignore___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_ignore___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_ignore___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_ignore___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_ignore___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_ignore___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_ignore___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_ignore___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_rcasesPat_ignore: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_ignore___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_clear___closed__0_value: LeanStringObject<6> =
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
        m_data: [99, 108, 101, 97, 114, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_clear___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_clear___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_rcasesPat_clear___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPat_clear___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_clear___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPat_clear___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_clear___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPat_clear___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_clear___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__5_value)
                as *mut LeanObject,
            1416858759244133794 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_rcasesPat_clear___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_clear___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_clear___closed__0_value)
                as *mut LeanObject,
            7163761142556626026 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_clear___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_clear___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_clear___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [45, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_clear___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_clear___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_clear___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_clear___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_clear___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_clear___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_clear___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_clear___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_clear___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_clear___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_clear___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_rcasesPat_clear: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_clear___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_explicit___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [101, 120, 112, 108, 105, 99, 105, 116, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_explicit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__0_value)
        as *mut LeanObject;
static l_Lean_Parser_Tactic_rcasesPat_explicit___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPat_explicit___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPat_explicit___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPat_explicit___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__5_value)
                as *mut LeanObject,
            1416858759244133794 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_rcasesPat_explicit___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__0_value)
                as *mut LeanObject,
            4085671085359500464 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_explicit___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_explicit___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [64, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_explicit___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_explicit___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_explicit___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_explicit___closed__4_value: LeanStringObject<5> =
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
        m_data: [110, 111, 87, 115, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_explicit___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_explicit___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__4_value)
                as *mut LeanObject,
            1581446985683836252 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_explicit___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_explicit___closed__6_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_explicit___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_explicit___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_explicit___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_explicit___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_explicit___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_explicit___closed__9_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_explicit___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__9_value)
        as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_rcasesPat_explicit: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_tuple___closed__0_value: LeanStringObject<6> =
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
        m_data: [116, 117, 112, 108, 101, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_tuple___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_rcasesPat_tuple___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPat_tuple___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPat_tuple___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPat_tuple___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__5_value)
                as *mut LeanObject,
            1416858759244133794 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_rcasesPat_tuple___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__0_value)
                as *mut LeanObject,
            6564809566780780850 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_tuple___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_tuple___closed__2_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 159, 168, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_tuple___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_tuple___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_tuple___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_tuple___closed__4_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [44, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_tuple___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_tuple___closed__5_value: LeanStringObject<3> =
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
        m_data: [44, 32, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_tuple___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_tuple___closed__6_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_tuple___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_tuple___closed__7_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 10,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__6_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_tuple___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_tuple___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_tuple___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_tuple___closed__9_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 159, 169, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_tuple___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_tuple___closed__10_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_tuple___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_tuple___closed__11_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_tuple___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_tuple___closed__12_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_tuple___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__12_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_rcasesPat_tuple: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_paren___closed__0_value: LeanStringObject<6> =
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
        m_data: [112, 97, 114, 101, 110, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_paren___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_paren___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_rcasesPat_paren___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPat_paren___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_paren___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPat_paren___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_paren___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rcasesPat_paren___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_paren___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__5_value)
                as *mut LeanObject,
            1416858759244133794 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_rcasesPat_paren___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_paren___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_paren___closed__0_value)
                as *mut LeanObject,
            9568303836005131977 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_paren___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_paren___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_paren___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [40, 0],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_paren___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_paren___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_paren___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_paren___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_paren___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_paren___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_paren___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_paren___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_paren___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_paren___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_paren___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_paren___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_paren___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_paren___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcasesPat_paren___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_paren___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_paren___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rcasesPat_paren___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_paren___closed__6_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_rcasesPat_paren: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_paren___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintroPat_quot___closed__0_value: LeanStringObject<10> =
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
        m_data: [114, 105, 110, 116, 114, 111, 80, 97, 116, 0],
    };
static mut l_Lean_Parser_Tactic_rintroPat_quot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_rintroPat_quot___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__0_value)
                as *mut LeanObject,
            1409078044207596393 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_rintroPat_quot___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__3_value)
                as *mut LeanObject,
            3430144869504617563 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rintroPat_quot___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintroPat_quot___closed__2_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            96, 40, 114, 105, 110, 116, 114, 111, 80, 97, 116, 124, 32, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_rintroPat_quot___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintroPat_quot___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rintroPat_quot___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintroPat_quot___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__0_value)
                as *mut LeanObject,
            1409078044207596393 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rintroPat_quot___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintroPat_quot___closed__5_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__4_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rintroPat_quot___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintroPat_quot___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rintroPat_quot___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintroPat_quot___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rintroPat_quot___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintroPat_quot___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rintroPat_quot___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintroPat_quot___closed__9_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__4_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rintroPat_quot___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_rintroPat_quot: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__9_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Category_rintroPat: *mut LeanObject = core::ptr::null_mut();
static l_Lean_Parser_Tactic_rintroPat_one___closed__0_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rintroPat_one___closed__0_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_one___closed__0_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rintroPat_one___closed__0_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_one___closed__0_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rintroPat_one___closed__0_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_one___closed__0_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__0_value)
                as *mut LeanObject,
            18291307736269544824 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_rintroPat_one___closed__0_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_one___closed__0_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_one___closed__0_value)
                as *mut LeanObject,
            4405638894356977192 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rintroPat_one___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_one___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintroPat_one___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_one___closed__0_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rintroPat_one___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_one___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_rintroPat_one: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_one___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintroPat_binder___closed__0_value: LeanStringObject<7> =
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
        m_data: [98, 105, 110, 100, 101, 114, 0],
    };
static mut l_Lean_Parser_Tactic_rintroPat_binder___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_rintroPat_binder___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rintroPat_binder___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rintroPat_binder___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__1_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Parser_Tactic_rintroPat_binder___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__0_value)
                as *mut LeanObject,
            18291307736269544824 as *mut LeanObject,
        ],
    };
pub static l_Lean_Parser_Tactic_rintroPat_binder___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__0_value)
                as *mut LeanObject,
            5873821271844280009 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rintroPat_binder___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintroPat_binder___closed__2_value: LeanStringObject<6> =
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
        m_data: [109, 97, 110, 121, 49, 0],
    };
static mut l_Lean_Parser_Tactic_rintroPat_binder___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintroPat_binder___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__2_value)
                as *mut LeanObject,
            17243740965612849207 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rintroPat_binder___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintroPat_binder___closed__4_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rintroPat_binder___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintroPat_binder___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_paren___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rintroPat_binder___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintroPat_binder___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rintroPat_binder___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintroPat_binder___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rintroPat_binder___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintroPat_binder___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_rintroPat_binder___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__8_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_rintroPat_binder: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcases___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [114, 99, 97, 115, 101, 115, 0],
};
static mut l_Lean_Parser_Tactic_rcases___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcases___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_rcases___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_rcases___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcases___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_rcases___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcases___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__1_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_rcases___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcases___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcases___closed__0_value) as *mut LeanObject,
        4285468744456948876 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_rcases___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcases___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcases___closed__2_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [114, 99, 97, 115, 101, 115, 32, 0],
};
static mut l_Lean_Parser_Tactic_rcases___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcases___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcases___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcases___closed__2_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_rcases___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcases___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_rcases___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_rcases___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_rcases___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_rcases___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_rcases___closed__6_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [32, 119, 105, 116, 104, 32, 0],
};
static mut l_Lean_Parser_Tactic_rcases___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcases___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcases___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_rcases___closed__6_value) as *mut LeanObject],
};
static mut l_Lean_Parser_Tactic_rcases___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcases___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcases___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcases___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_rcases___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcases___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rcases___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcases___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_rcases___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rcases___closed__9_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_rcases___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_rcases___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_rcases___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_rcases___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_rcases: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_obtain___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [111, 98, 116, 97, 105, 110, 0],
};
static mut l_Lean_Parser_Tactic_obtain___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_obtain___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_obtain___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_obtain___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__1_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_obtain___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__0_value) as *mut LeanObject,
        8171822449089818891 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_obtain___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_obtain___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_obtain___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_obtain___closed__3_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [112, 112, 83, 112, 97, 99, 101, 0],
};
static mut l_Lean_Parser_Tactic_obtain___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_obtain___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__3_value) as *mut LeanObject,
        17761616517784022991 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_obtain___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_obtain___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__4_value) as *mut LeanObject],
};
static mut l_Lean_Parser_Tactic_obtain___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_obtain___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_obtain___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_obtain___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_obtain___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_obtain___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_obtain___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_obtain___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_obtain___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_obtain___closed__10_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_Parser_Tactic_obtain___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_obtain___closed__11_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_obtain___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__11_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_obtain___closed__12_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 8) as u16,
        other: 3,
        tag: 11,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__4_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__6_value)
            as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_obtain___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__12_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_obtain___closed__13_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__11_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_obtain___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__13_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_obtain___closed__14_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__13_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_obtain___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__14_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_obtain___closed__15_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_obtain___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__15_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_obtain___closed__16_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__15_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_obtain___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__16_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_obtain: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__16_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintro___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [114, 105, 110, 116, 114, 111, 0],
};
static mut l_Lean_Parser_Tactic_rintro___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_rintro___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_rintro___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Parser_Tactic_rintro___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatMed___closed__1_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_Parser_Tactic_rintro___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__0_value) as *mut LeanObject,
        10592081902191181482 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_rintro___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintro___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__0_value) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_rintro___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintro___closed__3_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [99, 111, 108, 71, 116, 0],
};
static mut l_Lean_Parser_Tactic_rintro___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintro___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__3_value) as *mut LeanObject,
        17597206043415342265 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_rintro___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintro___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__4_value) as *mut LeanObject],
};
static mut l_Lean_Parser_Tactic_rintro___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintro___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_obtain___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_rintro___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintro___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_quot___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_rintro___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintro___closed__8_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rintroPat_binder___closed__3_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_rintro___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintro___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_rintro___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__9_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintro___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rcasesPatLo___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_rintro___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__10_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_rintro___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__1_value) as *mut LeanObject,
        (((1022 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_rintro___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__11_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_rintro: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_rintro___closed__11_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Parser_Category_rcasesPat() -> *mut LeanObject {
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    v___x_477_ = lean_box(0);
    return v___x_477_;
}
pub unsafe fn _init_l_Lean_Parser_Category_rintroPat() -> *mut LeanObject {
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    v___x_694_ = lean_box(0);
    return v___x_694_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_rcases___closed__4() -> *mut LeanObject {
    let mut v___x_746_: u8 = 0;
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    v___x_746_ = 0;
    v___x_747_ = l_Lean_Parser_Tactic_rcasesPat_tuple___closed__6;
    v___x_748_ = l_Lean_Parser_Tactic_rcasesPat_tuple___closed__4;
    v___x_749_ = l_Lean_Parser_Tactic_elimTarget;
    v___x_750_ = lean_alloc_ctor(10, 3, (1) as u32);
    lean_ctor_set(v___x_750_, 0, v___x_749_);
    lean_ctor_set(v___x_750_, 1, v___x_748_);
    lean_ctor_set(v___x_750_, 2, v___x_747_);
    lean_ctor_set_uint8(
        v___x_750_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_746_,
    );
    return v___x_750_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_rcases___closed__5() -> *mut LeanObject {
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    v___x_751_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_rcases___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_rcases___closed__4_once),
        _init_l_Lean_Parser_Tactic_rcases___closed__4,
    );
    v___x_752_ = l_Lean_Parser_Tactic_rcases___closed__3;
    v___x_753_ = l_Lean_Parser_Tactic_rcasesPat_quot___closed__8;
    v___x_754_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_754_, 0, v___x_753_);
    lean_ctor_set(v___x_754_, 1, v___x_752_);
    lean_ctor_set(v___x_754_, 2, v___x_751_);
    return v___x_754_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_rcases___closed__10() -> *mut LeanObject {
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    v___x_765_ = l_Lean_Parser_Tactic_rcases___closed__9;
    v___x_766_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_rcases___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_rcases___closed__5_once),
        _init_l_Lean_Parser_Tactic_rcases___closed__5,
    );
    v___x_767_ = l_Lean_Parser_Tactic_rcasesPat_quot___closed__8;
    v___x_768_ = lean_alloc_ctor(2, 3, (0) as u32);
    lean_ctor_set(v___x_768_, 0, v___x_767_);
    lean_ctor_set(v___x_768_, 1, v___x_766_);
    lean_ctor_set(v___x_768_, 2, v___x_765_);
    return v___x_768_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_rcases___closed__11() -> *mut LeanObject {
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    v___x_769_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_rcases___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_rcases___closed__10_once),
        _init_l_Lean_Parser_Tactic_rcases___closed__10,
    );
    v___x_770_ = lean_unsigned_to_nat(1022);
    v___x_771_ = l_Lean_Parser_Tactic_rcases___closed__1;
    v___x_772_ = lean_alloc_ctor(3, 3, (0) as u32);
    lean_ctor_set(v___x_772_, 0, v___x_771_);
    lean_ctor_set(v___x_772_, 1, v___x_770_);
    lean_ctor_set(v___x_772_, 2, v___x_769_);
    return v___x_772_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_rcases() -> *mut LeanObject {
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    v___x_773_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_rcases___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_rcases___closed__11_once),
        _init_l_Lean_Parser_Tactic_rcases___closed__11,
    );
    return v___x_773_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_RCases(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_RCases(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Parser_Category_rcasesPat = _init_l_Lean_Parser_Category_rcasesPat();
    lean_mark_persistent(l_Lean_Parser_Category_rcasesPat);
    l_Lean_Parser_Category_rintroPat = _init_l_Lean_Parser_Category_rintroPat();
    lean_mark_persistent(l_Lean_Parser_Category_rintroPat);
    l_Lean_Parser_Tactic_rcases = _init_l_Lean_Parser_Tactic_rcases();
    lean_mark_persistent(l_Lean_Parser_Tactic_rcases);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_RCases(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_RCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_RCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_RCases(builtin);
}
