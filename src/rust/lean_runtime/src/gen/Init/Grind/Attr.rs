// Lean compiler output
// Module: Init.Grind.Attr
// Imports: Init.Tactics
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
};
use crate::r#gen::Init::Tactics::{
    initialize_Init_Tactics, l_Lean_Parser_Tactic_simpPost, l_Lean_Parser_Tactic_simpPre,
    runtime_initialize_Init_Tactics,
};
pub static l_Lean_Parser_resetGrindAttrs___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Parser_resetGrindAttrs___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_resetGrindAttrs___closed__1_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Parser_resetGrindAttrs___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_resetGrindAttrs___closed__2_value: crate::leanh::LeanStringObject<16> =
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
            114, 101, 115, 101, 116, 71, 114, 105, 110, 100, 65, 116, 116, 114, 115, 0,
        ],
    };
static mut l_Lean_Parser_resetGrindAttrs___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_resetGrindAttrs___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_resetGrindAttrs___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_resetGrindAttrs___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__2_value)
                as *mut crate::leanh::LeanObject,
            10802873928890743578 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_resetGrindAttrs___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_resetGrindAttrs___closed__4_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            114, 101, 115, 101, 116, 95, 103, 114, 105, 110, 100, 95, 97, 116, 116, 114, 115, 37, 0,
        ],
    };
static mut l_Lean_Parser_resetGrindAttrs___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_resetGrindAttrs___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_resetGrindAttrs___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_resetGrindAttrs___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__3_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_resetGrindAttrs___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_resetGrindAttrs: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindGen___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [103, 114, 105, 110, 100, 71, 101, 110, 0],
    };
static mut l_Lean_Parser_Attr_grindGen___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindGen___closed__1_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [65, 116, 116, 114, 0],
    };
static mut l_Lean_Parser_Attr_grindGen___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindGen___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindGen___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindGen___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__2_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindGen___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__2_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9714501210324126650 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindGen___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindGen___closed__3_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [97, 110, 100, 116, 104, 101, 110, 0],
    };
static mut l_Lean_Parser_Attr_grindGen___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindGen___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__3_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindGen___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindGen___closed__5_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [112, 112, 83, 112, 97, 99, 101, 0],
    };
static mut l_Lean_Parser_Attr_grindGen___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindGen___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__5_value)
                as *mut crate::leanh::LeanObject,
            17761616517784022991 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindGen___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindGen___closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindGen___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindGen___closed__8_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [103, 101, 110, 0],
    };
static mut l_Lean_Parser_Attr_grindGen___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindGen___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__8_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindGen___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindGen___closed__10_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindGen___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindGen___closed__11_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindGen___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Attr_grindGen: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEq___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [103, 114, 105, 110, 100, 69, 113, 0],
    };
static mut l_Lean_Parser_Attr_grindEq___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindEq___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindEq___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindEq___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindEq___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14718087869874512563 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEq___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEq___closed__2_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [61, 0],
    };
static mut l_Lean_Parser_Attr_grindEq___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEq___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEq___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEq___closed__4_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Parser_Attr_grindEq___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEq___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__4_value)
                as *mut crate::leanh::LeanObject,
            18170484695678750185 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEq___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEq___closed__6_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEq___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEq___closed__7_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEq___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEq___closed__8_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEq___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Attr_grindEq: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqRhs___closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [103, 114, 105, 110, 100, 69, 113, 82, 104, 115, 0],
    };
static mut l_Lean_Parser_Attr_grindEqRhs___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindEqRhs___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindEqRhs___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindEqRhs___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindEqRhs___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            4956164565610314718 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqRhs___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqRhs___closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [97, 116, 111, 109, 105, 99, 0],
    };
static mut l_Lean_Parser_Attr_grindEqRhs___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqRhs___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__2_value)
                as *mut crate::leanh::LeanObject,
            4024150434455327032 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqRhs___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqRhs___closed__4_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Parser_Attr_grindEqRhs___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqRhs___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqRhs___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqRhs___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqRhs___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqRhs___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqRhs___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqRhs___closed__8_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqRhs___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqRhs___closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqRhs___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Attr_grindEqRhs: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBoth___closed__0_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [103, 114, 105, 110, 100, 69, 113, 66, 111, 116, 104, 0],
    };
static mut l_Lean_Parser_Attr_grindEqBoth___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindEqBoth___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindEqBoth___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindEqBoth___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindEqBoth___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9254304300027733583 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBoth___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBoth___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBoth___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBoth___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBoth___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBoth___closed__4_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBoth___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBoth___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBoth___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBoth___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBoth___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Attr_grindEqBoth: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBoth___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [103, 114, 105, 110, 100, 69, 113, 66, 119, 100, 0],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindEqBwd___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindEqBwd___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindEqBwd___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindEqBwd___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__0_value)
                as *mut crate::leanh::LeanObject,
            3844513800486599162 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__2_value: crate::leanh::LeanStringObject<14> =
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
        m_data: [
            112, 97, 116, 116, 101, 114, 110, 73, 103, 110, 111, 114, 101, 0,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__2_value)
                as *mut crate::leanh::LeanObject,
            17328449285856252867 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__4_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [111, 114, 101, 108, 115, 101, 0],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__4_value)
                as *mut crate::leanh::LeanObject,
            393173242845875278 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__6_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [103, 114, 111, 117, 112, 0],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__6_value)
                as *mut crate::leanh::LeanObject,
            2214559063752339918 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__8_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 134, 144, 0],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__9_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__10_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__11_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__12_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__13_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [60, 45, 0],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__14_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__15_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__14_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__16_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__17_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__18_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__12_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__17_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__19_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindEqBwd___closed__20_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindEqBwd___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Attr_grindEqBwd: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindBwd___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [103, 114, 105, 110, 100, 66, 119, 100, 0],
    };
static mut l_Lean_Parser_Attr_grindBwd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindBwd___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindBwd___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindBwd___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindBwd___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__0_value)
                as *mut crate::leanh::LeanObject,
            1689458581469504370 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindBwd___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindBwd___closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [116, 111, 107, 101, 110, 0],
    };
static mut l_Lean_Parser_Attr_grindBwd___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindBwd___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value)
                as *mut crate::leanh::LeanObject,
            9392652980833654105 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindBwd___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__8_value)
                as *mut crate::leanh::LeanObject,
            9149852190130109334 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindBwd___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindBwd___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindBwd___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindBwd___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value)
                as *mut crate::leanh::LeanObject,
            9392652980833654105 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindBwd___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__5_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__13_value)
                as *mut crate::leanh::LeanObject,
            1297364225897356313 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindBwd___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindBwd___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__13_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindBwd___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindBwd___closed__7_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindBwd___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindBwd___closed__8_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindBwd___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindBwd___closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindBwd___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindBwd___closed__10_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindBwd___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Attr_grindBwd: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindFwd___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [103, 114, 105, 110, 100, 70, 119, 100, 0],
    };
static mut l_Lean_Parser_Attr_grindFwd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindFwd___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindFwd___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindFwd___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindFwd___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__0_value)
                as *mut crate::leanh::LeanObject,
            3412781221517828473 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindFwd___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindFwd___closed__2_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 134, 146, 0],
    };
static mut l_Lean_Parser_Attr_grindFwd___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindFwd___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value)
                as *mut crate::leanh::LeanObject,
            9392652980833654105 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindFwd___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__2_value)
                as *mut crate::leanh::LeanObject,
            11707734540142241164 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindFwd___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindFwd___closed__4_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindFwd___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindFwd___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindFwd___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindFwd___closed__6_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [45, 62, 0],
    };
static mut l_Lean_Parser_Attr_grindFwd___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindFwd___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value)
                as *mut crate::leanh::LeanObject,
            9392652980833654105 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindFwd___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__6_value)
                as *mut crate::leanh::LeanObject,
            9958343667474391476 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindFwd___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindFwd___closed__8_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindFwd___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindFwd___closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindFwd___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindFwd___closed__10_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindFwd___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindFwd___closed__11_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindFwd___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindFwd___closed__12_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindFwd___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Attr_grindFwd: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFwd___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindRL___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [103, 114, 105, 110, 100, 82, 76, 0],
    };
static mut l_Lean_Parser_Attr_grindRL___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindRL___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindRL___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindRL___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindRL___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14783791908340461652 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindRL___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindRL___closed__2_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 135, 144, 0],
    };
static mut l_Lean_Parser_Attr_grindRL___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindRL___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value)
                as *mut crate::leanh::LeanObject,
            9392652980833654105 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindRL___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__2_value)
                as *mut crate::leanh::LeanObject,
            17529940758261935356 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindRL___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindRL___closed__4_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindRL___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindRL___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindRL___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindRL___closed__6_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [60, 61, 0],
    };
static mut l_Lean_Parser_Attr_grindRL___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindRL___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value)
                as *mut crate::leanh::LeanObject,
            9392652980833654105 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindRL___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__6_value)
                as *mut crate::leanh::LeanObject,
            8722646758108166465 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindRL___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindRL___closed__8_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindRL___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindRL___closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindRL___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindRL___closed__10_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindRL___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindRL___closed__11_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindRL___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindRL___closed__12_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindRL___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Attr_grindRL: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindRL___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindLR___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [103, 114, 105, 110, 100, 76, 82, 0],
    };
static mut l_Lean_Parser_Attr_grindLR___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindLR___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindLR___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindLR___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindLR___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11844982159682858904 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindLR___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindLR___closed__2_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 135, 146, 0],
    };
static mut l_Lean_Parser_Attr_grindLR___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindLR___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value)
                as *mut crate::leanh::LeanObject,
            9392652980833654105 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindLR___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__2_value)
                as *mut crate::leanh::LeanObject,
            17456214878486818065 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindLR___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindLR___closed__4_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindLR___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindLR___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindLR___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindLR___closed__6_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [61, 62, 0],
    };
static mut l_Lean_Parser_Attr_grindLR___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindLR___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value)
                as *mut crate::leanh::LeanObject,
            9392652980833654105 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindLR___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__6_value)
                as *mut crate::leanh::LeanObject,
            5713651635530161729 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindLR___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindLR___closed__8_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindLR___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindLR___closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindLR___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindLR___closed__10_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindLR___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindLR___closed__11_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindLR___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindLR___closed__12_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindLR___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Attr_grindLR: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindLR___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindDef___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [103, 114, 105, 110, 100, 68, 101, 102, 0],
    };
static mut l_Lean_Parser_Attr_grindDef___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindDef___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindDef___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindDef___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindDef___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5549592694638828098 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindDef___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindDef___closed__2_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [46, 0],
    };
static mut l_Lean_Parser_Attr_grindDef___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindDef___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value)
                as *mut crate::leanh::LeanObject,
            9392652980833654105 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindDef___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2511666537814787754 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindDef___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindDef___closed__4_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindDef___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindDef___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindDef___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindDef___closed__6_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 1,
        m_data: [194, 183, 0],
    };
static mut l_Lean_Parser_Attr_grindDef___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindDef___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value)
                as *mut crate::leanh::LeanObject,
            9392652980833654105 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindDef___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__6_value)
                as *mut crate::leanh::LeanObject,
            16697830463868302406 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindDef___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindDef___closed__8_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindDef___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindDef___closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindDef___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindDef___closed__10_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindDef___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindDef___closed__11_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindDef___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindDef___closed__12_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__11_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindDef___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindDef___closed__13_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindDef___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Attr_grindDef: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindUsr___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [103, 114, 105, 110, 100, 85, 115, 114, 0],
    };
static mut l_Lean_Parser_Attr_grindUsr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindUsr___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindUsr___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindUsr___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindUsr___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__0_value)
                as *mut crate::leanh::LeanObject,
            1329309285596805836 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindUsr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindUsr___closed__2_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [117, 115, 114, 0],
    };
static mut l_Lean_Parser_Attr_grindUsr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindUsr___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindUsr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindUsr___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindUsr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Attr_grindUsr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUsr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindCases___closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [103, 114, 105, 110, 100, 67, 97, 115, 101, 115, 0],
    };
static mut l_Lean_Parser_Attr_grindCases___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindCases___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindCases___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindCases___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindCases___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11737843193706483285 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindCases___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindCases___closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [99, 97, 115, 101, 115, 0],
    };
static mut l_Lean_Parser_Attr_grindCases___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindCases___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindCases___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindCases___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindCases___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Attr_grindCases: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindCasesEager___closed__0_value: crate::leanh::LeanStringObject<
    16,
> = crate::leanh::LeanStringObject {
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
        103, 114, 105, 110, 100, 67, 97, 115, 101, 115, 69, 97, 103, 101, 114, 0,
    ],
};
static mut l_Lean_Parser_Attr_grindCasesEager___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindCasesEager___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindCasesEager___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindCasesEager___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindCasesEager___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5084203056696709707 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindCasesEager___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindCasesEager___closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [101, 97, 103, 101, 114, 0],
    };
static mut l_Lean_Parser_Attr_grindCasesEager___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindCasesEager___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindCasesEager___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindCasesEager___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCases___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindCasesEager___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindCasesEager___closed__5_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqRhs___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindCasesEager___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindCasesEager___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindCasesEager___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Attr_grindCasesEager: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindCasesEager___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindIntro___closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [103, 114, 105, 110, 100, 73, 110, 116, 114, 111, 0],
    };
static mut l_Lean_Parser_Attr_grindIntro___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindIntro___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindIntro___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindIntro___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindIntro___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9959989771779604110 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindIntro___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindIntro___closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [105, 110, 116, 114, 111, 0],
    };
static mut l_Lean_Parser_Attr_grindIntro___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindIntro___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindIntro___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindIntro___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindIntro___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Attr_grindIntro: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindIntro___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindExt___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [103, 114, 105, 110, 100, 69, 120, 116, 0],
    };
static mut l_Lean_Parser_Attr_grindExt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindExt___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindExt___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindExt___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindExt___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__0_value)
                as *mut crate::leanh::LeanObject,
            18276616586504290707 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindExt___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindExt___closed__2_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [101, 120, 116, 0],
    };
static mut l_Lean_Parser_Attr_grindExt___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindExt___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindExt___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindExt___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindExt___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Attr_grindExt: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindExt___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindInj___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [103, 114, 105, 110, 100, 73, 110, 106, 0],
    };
static mut l_Lean_Parser_Attr_grindInj___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindInj___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindInj___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindInj___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindInj___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13947935108849328607 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindInj___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindInj___closed__2_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [105, 110, 106, 0],
    };
static mut l_Lean_Parser_Attr_grindInj___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindInj___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindInj___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindInj___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindInj___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Attr_grindInj: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindInj___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindFunCC___closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [103, 114, 105, 110, 100, 70, 117, 110, 67, 67, 0],
    };
static mut l_Lean_Parser_Attr_grindFunCC___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindFunCC___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindFunCC___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindFunCC___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindFunCC___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__0_value)
                as *mut crate::leanh::LeanObject,
            3120519524940125401 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindFunCC___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindFunCC___closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [102, 117, 110, 67, 67, 0],
    };
static mut l_Lean_Parser_Attr_grindFunCC___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindFunCC___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindFunCC___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindFunCC___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindFunCC___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Attr_grindFunCC: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindFunCC___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindNorm___closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [103, 114, 105, 110, 100, 78, 111, 114, 109, 0],
    };
static mut l_Lean_Parser_Attr_grindNorm___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindNorm___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindNorm___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindNorm___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindNorm___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__0_value)
                as *mut crate::leanh::LeanObject,
            10672965319075724966 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindNorm___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindNorm___closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [110, 111, 114, 109, 0],
    };
static mut l_Lean_Parser_Attr_grindNorm___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindNorm___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindNorm___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_grindNorm___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindNorm___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindNorm___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindNorm___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindNorm___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindNorm___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Attr_grindNorm___closed__7_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 2,
        m_data: [226, 134, 144, 32, 0],
    };
static mut l_Lean_Parser_Attr_grindNorm___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindNorm___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value)
                as *mut crate::leanh::LeanObject,
            9392652980833654105 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindNorm___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__8_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__7_value)
                as *mut crate::leanh::LeanObject,
            5265644217102624940 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindNorm___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindNorm___closed__9_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindNorm___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindNorm___closed__10_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindNorm___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindNorm___closed__11_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [60, 45, 32, 0],
    };
static mut l_Lean_Parser_Attr_grindNorm___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__11_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindNorm___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindBwd___closed__2_value)
                as *mut crate::leanh::LeanObject,
            9392652980833654105 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindNorm___closed__12_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__12_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__11_value)
                as *mut crate::leanh::LeanObject,
            11081745058534201334 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindNorm___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindNorm___closed__13_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindNorm___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindNorm___closed__14_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__11_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__12_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindNorm___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindNorm___closed__15_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindNorm___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindNorm___closed__16_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindNorm___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindNorm___closed__17_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEq___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindNorm___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindNorm___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_grindNorm___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindNorm___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindNorm___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindNorm___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_grindNorm: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Attr_grindUnfold___closed__0_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [103, 114, 105, 110, 100, 85, 110, 102, 111, 108, 100, 0],
    };
static mut l_Lean_Parser_Attr_grindUnfold___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindUnfold___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindUnfold___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindUnfold___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindUnfold___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15827030602716394966 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindUnfold___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindUnfold___closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [117, 110, 102, 111, 108, 100, 0],
    };
static mut l_Lean_Parser_Attr_grindUnfold___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindUnfold___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindUnfold___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindUnfold___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindUnfold___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Attr_grindUnfold: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindSym___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [103, 114, 105, 110, 100, 83, 121, 109, 0],
    };
static mut l_Lean_Parser_Attr_grindSym___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindSym___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindSym___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindSym___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindSym___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__0_value)
                as *mut crate::leanh::LeanObject,
            1728939392783600744 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindSym___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindSym___closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [115, 121, 109, 98, 111, 108, 0],
    };
static mut l_Lean_Parser_Attr_grindSym___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindSym___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindSym___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindSym___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindSym___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindSym___closed__5_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [112, 114, 105, 111, 0],
    };
static mut l_Lean_Parser_Attr_grindSym___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindSym___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__5_value)
                as *mut crate::leanh::LeanObject,
            17836958171642591098 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindSym___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindSym___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__6_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindSym___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindSym___closed__8_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindSym___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindSym___closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindSym___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Attr_grindSym: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindSym___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindMod___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [103, 114, 105, 110, 100, 77, 111, 100, 0],
    };
static mut l_Lean_Parser_Attr_grindMod___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindMod___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grindMod___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindMod___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindMod___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grindMod___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindMod___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grindMod___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindMod___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindMod___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8580387018487626918 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindMod___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindMod___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grindMod___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindEqBwd___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindUnfold___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindDef___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grindMod___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grindMod___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_grindMod___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindMod___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindMod___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindMod___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindMod___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindMod___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindMod___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindMod___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindMod___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindMod___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindMod___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindMod___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindMod___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindMod___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindMod___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindMod___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindMod___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindMod___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindMod___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grindMod___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grindMod___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_grindMod: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Attr_grind___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [103, 114, 105, 110, 100, 0],
    };
static mut l_Lean_Parser_Attr_grind___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grind___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grind___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grind___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grind___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grind___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grind___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grind___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grind___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6111248473341059083 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grind___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grind___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grind___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grind___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_grind___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grind___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grind___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grind___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grind___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grind___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grind___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grind___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_grind: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Attr_grind_x21___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [103, 114, 105, 110, 100, 33, 0],
    };
static mut l_Lean_Parser_Attr_grind_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grind_x21___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grind_x21___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grind_x21___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grind_x21___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15278515049066527744 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grind_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grind_x21___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grind_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_grind_x21___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grind_x21___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grind_x21___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grind_x21___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_grind_x21: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Attr_grind_x3f___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [103, 114, 105, 110, 100, 63, 0],
    };
static mut l_Lean_Parser_Attr_grind_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grind_x3f___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grind_x3f___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x3f___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grind_x3f___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x3f___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grind_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x3f___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14609666066721317603 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grind_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grind_x3f___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grind_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_grind_x3f___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grind_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grind_x3f___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grind_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_grind_x3f: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Attr_grind_x21_x3f___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [103, 114, 105, 110, 100, 33, 63, 0],
    };
static mut l_Lean_Parser_Attr_grind_x21_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_grind_x21_x3f___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grind_x21_x3f___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21_x3f___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_resetGrindAttrs___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_grind_x21_x3f___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21_x3f___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grindGen___closed__1_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_grind_x21_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21_x3f___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12064337937714458527 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grind_x21_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_grind_x21_x3f___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_grind_x21_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_grind_x21_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_grind_x21_x3f___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grind_x21_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_grind_x21_x3f___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_grind_x21_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_grind_x21_x3f: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Grind_genPattern___redArg(
    mut v_x_776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_776_);
    return v_x_776_;
}
pub unsafe fn l_Lean_Grind_genPattern___redArg___boxed(
    mut v_x_777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_778_ = l_Lean_Grind_genPattern___redArg(v_x_777_);
    crate::leanh::lean_dec(v_x_777_);
    return v_res_778_;
}
pub unsafe fn l_Lean_Grind_genPattern(
    mut v_00_u03b1_779_: *mut crate::leanh::LeanObject,
    mut v___h_780_: *mut crate::leanh::LeanObject,
    mut v_x_781_: *mut crate::leanh::LeanObject,
    mut v___val_782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_781_);
    return v_x_781_;
}
pub unsafe fn l_Lean_Grind_genPattern___boxed(
    mut v_00_u03b1_783_: *mut crate::leanh::LeanObject,
    mut v___h_784_: *mut crate::leanh::LeanObject,
    mut v_x_785_: *mut crate::leanh::LeanObject,
    mut v___val_786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_787_ = l_Lean_Grind_genPattern(v_00_u03b1_783_, v___h_784_, v_x_785_, v___val_786_);
    crate::leanh::lean_dec(v___val_786_);
    crate::leanh::lean_dec(v_x_785_);
    return v_res_787_;
}
pub unsafe fn l_Lean_Grind_genHEqPattern___redArg(
    mut v_x_788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_788_);
    return v_x_788_;
}
pub unsafe fn l_Lean_Grind_genHEqPattern___redArg___boxed(
    mut v_x_789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_790_ = l_Lean_Grind_genHEqPattern___redArg(v_x_789_);
    crate::leanh::lean_dec(v_x_789_);
    return v_res_790_;
}
pub unsafe fn l_Lean_Grind_genHEqPattern(
    mut v_00_u03b1_791_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_792_: *mut crate::leanh::LeanObject,
    mut v___h_793_: *mut crate::leanh::LeanObject,
    mut v_x_794_: *mut crate::leanh::LeanObject,
    mut v___val_795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_794_);
    return v_x_794_;
}
pub unsafe fn l_Lean_Grind_genHEqPattern___boxed(
    mut v_00_u03b1_796_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_797_: *mut crate::leanh::LeanObject,
    mut v___h_798_: *mut crate::leanh::LeanObject,
    mut v_x_799_: *mut crate::leanh::LeanObject,
    mut v___val_800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_801_ = l_Lean_Grind_genHEqPattern(
        v_00_u03b1_796_,
        v_00_u03b2_797_,
        v___h_798_,
        v_x_799_,
        v___val_800_,
    );
    crate::leanh::lean_dec(v___val_800_);
    crate::leanh::lean_dec(v_x_799_);
    return v_res_801_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindNorm___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1291_ = l_Lean_Parser_Tactic_simpPost;
    v___x_1292_ = l_Lean_Parser_Tactic_simpPre;
    v___x_1293_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1294_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1294_, 0, v___x_1293_);
    crate::leanh::lean_ctor_set(v___x_1294_, 1, v___x_1292_);
    crate::leanh::lean_ctor_set(v___x_1294_, 2, v___x_1291_);
    return v___x_1294_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindNorm___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1295_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindNorm___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindNorm___closed__4_once),
        _init_l_Lean_Parser_Attr_grindNorm___closed__4,
    );
    v___x_1296_ = l_Lean_Parser_Attr_grindEq___closed__5;
    v___x_1297_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1297_, 0, v___x_1296_);
    crate::leanh::lean_ctor_set(v___x_1297_, 1, v___x_1295_);
    return v___x_1297_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindNorm___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1298_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindNorm___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindNorm___closed__5_once),
        _init_l_Lean_Parser_Attr_grindNorm___closed__5,
    );
    v___x_1299_ = l_Lean_Parser_Attr_grindNorm___closed__3;
    v___x_1300_ = l_Lean_Parser_Attr_grindGen___closed__4;
    v___x_1301_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1301_, 0, v___x_1300_);
    crate::leanh::lean_ctor_set(v___x_1301_, 1, v___x_1299_);
    crate::leanh::lean_ctor_set(v___x_1301_, 2, v___x_1298_);
    return v___x_1301_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindNorm___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1332_ = l_Lean_Parser_Attr_grindNorm___closed__17;
    v___x_1333_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindNorm___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindNorm___closed__6_once),
        _init_l_Lean_Parser_Attr_grindNorm___closed__6,
    );
    v___x_1334_ = l_Lean_Parser_Attr_grindGen___closed__4;
    v___x_1335_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1335_, 0, v___x_1334_);
    crate::leanh::lean_ctor_set(v___x_1335_, 1, v___x_1333_);
    crate::leanh::lean_ctor_set(v___x_1335_, 2, v___x_1332_);
    return v___x_1335_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindNorm___closed__19() -> *mut crate::leanh::LeanObject {
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1336_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindNorm___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindNorm___closed__18_once),
        _init_l_Lean_Parser_Attr_grindNorm___closed__18,
    );
    v___x_1337_ = l_Lean_Parser_Attr_grindNorm___closed__1;
    v___x_1338_ = l_Lean_Parser_Attr_grindNorm___closed__0;
    v___x_1339_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1339_, 0, v___x_1338_);
    crate::leanh::lean_ctor_set(v___x_1339_, 1, v___x_1337_);
    crate::leanh::lean_ctor_set(v___x_1339_, 2, v___x_1336_);
    return v___x_1339_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindNorm() -> *mut crate::leanh::LeanObject {
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1340_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindNorm___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindNorm___closed__19_once),
        _init_l_Lean_Parser_Attr_grindNorm___closed__19,
    );
    return v___x_1340_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1395_ = l_Lean_Parser_Attr_grindMod___closed__2;
    v___x_1396_ = l_Lean_Parser_Attr_grindNorm;
    v___x_1397_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1398_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1398_, 0, v___x_1397_);
    crate::leanh::lean_ctor_set(v___x_1398_, 1, v___x_1396_);
    crate::leanh::lean_ctor_set(v___x_1398_, 2, v___x_1395_);
    return v___x_1398_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1399_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__3_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__3,
    );
    v___x_1400_ = l_Lean_Parser_Attr_grindFunCC;
    v___x_1401_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1402_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1402_, 0, v___x_1401_);
    crate::leanh::lean_ctor_set(v___x_1402_, 1, v___x_1400_);
    crate::leanh::lean_ctor_set(v___x_1402_, 2, v___x_1399_);
    return v___x_1402_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1403_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__4_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__4,
    );
    v___x_1404_ = l_Lean_Parser_Attr_grindInj;
    v___x_1405_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1406_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1406_, 0, v___x_1405_);
    crate::leanh::lean_ctor_set(v___x_1406_, 1, v___x_1404_);
    crate::leanh::lean_ctor_set(v___x_1406_, 2, v___x_1403_);
    return v___x_1406_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1407_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__5_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__5,
    );
    v___x_1408_ = l_Lean_Parser_Attr_grindSym;
    v___x_1409_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1410_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1410_, 0, v___x_1409_);
    crate::leanh::lean_ctor_set(v___x_1410_, 1, v___x_1408_);
    crate::leanh::lean_ctor_set(v___x_1410_, 2, v___x_1407_);
    return v___x_1410_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1411_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__6_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__6,
    );
    v___x_1412_ = l_Lean_Parser_Attr_grindGen;
    v___x_1413_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1414_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1414_, 0, v___x_1413_);
    crate::leanh::lean_ctor_set(v___x_1414_, 1, v___x_1412_);
    crate::leanh::lean_ctor_set(v___x_1414_, 2, v___x_1411_);
    return v___x_1414_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1415_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__7_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__7,
    );
    v___x_1416_ = l_Lean_Parser_Attr_grindExt;
    v___x_1417_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1418_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1418_, 0, v___x_1417_);
    crate::leanh::lean_ctor_set(v___x_1418_, 1, v___x_1416_);
    crate::leanh::lean_ctor_set(v___x_1418_, 2, v___x_1415_);
    return v___x_1418_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1419_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__8_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__8,
    );
    v___x_1420_ = l_Lean_Parser_Attr_grindIntro;
    v___x_1421_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1422_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1422_, 0, v___x_1421_);
    crate::leanh::lean_ctor_set(v___x_1422_, 1, v___x_1420_);
    crate::leanh::lean_ctor_set(v___x_1422_, 2, v___x_1419_);
    return v___x_1422_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1423_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__9_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__9,
    );
    v___x_1424_ = l_Lean_Parser_Attr_grindCases;
    v___x_1425_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1426_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1426_, 0, v___x_1425_);
    crate::leanh::lean_ctor_set(v___x_1426_, 1, v___x_1424_);
    crate::leanh::lean_ctor_set(v___x_1426_, 2, v___x_1423_);
    return v___x_1426_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__11() -> *mut crate::leanh::LeanObject {
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1427_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__10_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__10,
    );
    v___x_1428_ = l_Lean_Parser_Attr_grindCasesEager;
    v___x_1429_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1430_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1430_, 0, v___x_1429_);
    crate::leanh::lean_ctor_set(v___x_1430_, 1, v___x_1428_);
    crate::leanh::lean_ctor_set(v___x_1430_, 2, v___x_1427_);
    return v___x_1430_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1431_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__11_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__11,
    );
    v___x_1432_ = l_Lean_Parser_Attr_grindUsr;
    v___x_1433_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1434_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1434_, 0, v___x_1433_);
    crate::leanh::lean_ctor_set(v___x_1434_, 1, v___x_1432_);
    crate::leanh::lean_ctor_set(v___x_1434_, 2, v___x_1431_);
    return v___x_1434_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1435_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__12_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__12,
    );
    v___x_1436_ = l_Lean_Parser_Attr_grindLR;
    v___x_1437_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1438_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1438_, 0, v___x_1437_);
    crate::leanh::lean_ctor_set(v___x_1438_, 1, v___x_1436_);
    crate::leanh::lean_ctor_set(v___x_1438_, 2, v___x_1435_);
    return v___x_1438_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__14() -> *mut crate::leanh::LeanObject {
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1439_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__13_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__13,
    );
    v___x_1440_ = l_Lean_Parser_Attr_grindRL;
    v___x_1441_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1442_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1442_, 0, v___x_1441_);
    crate::leanh::lean_ctor_set(v___x_1442_, 1, v___x_1440_);
    crate::leanh::lean_ctor_set(v___x_1442_, 2, v___x_1439_);
    return v___x_1442_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__15() -> *mut crate::leanh::LeanObject {
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1443_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__14_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__14,
    );
    v___x_1444_ = l_Lean_Parser_Attr_grindFwd;
    v___x_1445_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1446_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1446_, 0, v___x_1445_);
    crate::leanh::lean_ctor_set(v___x_1446_, 1, v___x_1444_);
    crate::leanh::lean_ctor_set(v___x_1446_, 2, v___x_1443_);
    return v___x_1446_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__16() -> *mut crate::leanh::LeanObject {
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1447_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__15_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__15,
    );
    v___x_1448_ = l_Lean_Parser_Attr_grindBwd;
    v___x_1449_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1450_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1450_, 0, v___x_1449_);
    crate::leanh::lean_ctor_set(v___x_1450_, 1, v___x_1448_);
    crate::leanh::lean_ctor_set(v___x_1450_, 2, v___x_1447_);
    return v___x_1450_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__17() -> *mut crate::leanh::LeanObject {
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1451_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__16_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__16,
    );
    v___x_1452_ = l_Lean_Parser_Attr_grindEqBwd;
    v___x_1453_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1454_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1454_, 0, v___x_1453_);
    crate::leanh::lean_ctor_set(v___x_1454_, 1, v___x_1452_);
    crate::leanh::lean_ctor_set(v___x_1454_, 2, v___x_1451_);
    return v___x_1454_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1455_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__17_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__17,
    );
    v___x_1456_ = l_Lean_Parser_Attr_grindEq;
    v___x_1457_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1458_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1458_, 0, v___x_1457_);
    crate::leanh::lean_ctor_set(v___x_1458_, 1, v___x_1456_);
    crate::leanh::lean_ctor_set(v___x_1458_, 2, v___x_1455_);
    return v___x_1458_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__19() -> *mut crate::leanh::LeanObject {
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1459_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__18_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__18,
    );
    v___x_1460_ = l_Lean_Parser_Attr_grindEqRhs;
    v___x_1461_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1462_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1462_, 0, v___x_1461_);
    crate::leanh::lean_ctor_set(v___x_1462_, 1, v___x_1460_);
    crate::leanh::lean_ctor_set(v___x_1462_, 2, v___x_1459_);
    return v___x_1462_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__20() -> *mut crate::leanh::LeanObject {
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1463_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__19_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__19,
    );
    v___x_1464_ = l_Lean_Parser_Attr_grindEqBoth;
    v___x_1465_ = l_Lean_Parser_Attr_grindEqBwd___closed__5;
    v___x_1466_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1466_, 0, v___x_1465_);
    crate::leanh::lean_ctor_set(v___x_1466_, 1, v___x_1464_);
    crate::leanh::lean_ctor_set(v___x_1466_, 2, v___x_1463_);
    return v___x_1466_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod___closed__21() -> *mut crate::leanh::LeanObject {
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1467_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__20_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__20,
    );
    v___x_1468_ = l_Lean_Parser_Attr_grindMod___closed__1;
    v___x_1469_ = l_Lean_Parser_Attr_grindMod___closed__0;
    v___x_1470_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1470_, 0, v___x_1469_);
    crate::leanh::lean_ctor_set(v___x_1470_, 1, v___x_1468_);
    crate::leanh::lean_ctor_set(v___x_1470_, 2, v___x_1467_);
    return v___x_1470_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grindMod() -> *mut crate::leanh::LeanObject {
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1471_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grindMod___closed__21_once),
        _init_l_Lean_Parser_Attr_grindMod___closed__21,
    );
    return v___x_1471_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1481_ = l_Lean_Parser_Attr_grindMod;
    v___x_1482_ = l_Lean_Parser_Attr_grindGen___closed__7;
    v___x_1483_ = l_Lean_Parser_Attr_grindGen___closed__4;
    v___x_1484_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1484_, 0, v___x_1483_);
    crate::leanh::lean_ctor_set(v___x_1484_, 1, v___x_1482_);
    crate::leanh::lean_ctor_set(v___x_1484_, 2, v___x_1481_);
    return v___x_1484_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1485_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__3_once),
        _init_l_Lean_Parser_Attr_grind___closed__3,
    );
    v___x_1486_ = l_Lean_Parser_Attr_grindEq___closed__5;
    v___x_1487_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1487_, 0, v___x_1486_);
    crate::leanh::lean_ctor_set(v___x_1487_, 1, v___x_1485_);
    return v___x_1487_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1488_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__4_once),
        _init_l_Lean_Parser_Attr_grind___closed__4,
    );
    v___x_1489_ = l_Lean_Parser_Attr_grind___closed__2;
    v___x_1490_ = l_Lean_Parser_Attr_grindGen___closed__4;
    v___x_1491_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1491_, 0, v___x_1490_);
    crate::leanh::lean_ctor_set(v___x_1491_, 1, v___x_1489_);
    crate::leanh::lean_ctor_set(v___x_1491_, 2, v___x_1488_);
    return v___x_1491_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1492_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__5_once),
        _init_l_Lean_Parser_Attr_grind___closed__5,
    );
    v___x_1493_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_1494_ = l_Lean_Parser_Attr_grind___closed__1;
    v___x_1495_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1495_, 0, v___x_1494_);
    crate::leanh::lean_ctor_set(v___x_1495_, 1, v___x_1493_);
    crate::leanh::lean_ctor_set(v___x_1495_, 2, v___x_1492_);
    return v___x_1495_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind() -> *mut crate::leanh::LeanObject {
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1496_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__6_once),
        _init_l_Lean_Parser_Attr_grind___closed__6,
    );
    return v___x_1496_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind_x21___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1506_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__4_once),
        _init_l_Lean_Parser_Attr_grind___closed__4,
    );
    v___x_1507_ = l_Lean_Parser_Attr_grind_x21___closed__2;
    v___x_1508_ = l_Lean_Parser_Attr_grindGen___closed__4;
    v___x_1509_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1509_, 0, v___x_1508_);
    crate::leanh::lean_ctor_set(v___x_1509_, 1, v___x_1507_);
    crate::leanh::lean_ctor_set(v___x_1509_, 2, v___x_1506_);
    return v___x_1509_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind_x21___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1510_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x21___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x21___closed__3_once),
        _init_l_Lean_Parser_Attr_grind_x21___closed__3,
    );
    v___x_1511_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_1512_ = l_Lean_Parser_Attr_grind_x21___closed__1;
    v___x_1513_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1513_, 0, v___x_1512_);
    crate::leanh::lean_ctor_set(v___x_1513_, 1, v___x_1511_);
    crate::leanh::lean_ctor_set(v___x_1513_, 2, v___x_1510_);
    return v___x_1513_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind_x21() -> *mut crate::leanh::LeanObject {
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1514_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x21___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x21___closed__4_once),
        _init_l_Lean_Parser_Attr_grind_x21___closed__4,
    );
    return v___x_1514_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind_x3f___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1524_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__4_once),
        _init_l_Lean_Parser_Attr_grind___closed__4,
    );
    v___x_1525_ = l_Lean_Parser_Attr_grind_x3f___closed__2;
    v___x_1526_ = l_Lean_Parser_Attr_grindGen___closed__4;
    v___x_1527_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1527_, 0, v___x_1526_);
    crate::leanh::lean_ctor_set(v___x_1527_, 1, v___x_1525_);
    crate::leanh::lean_ctor_set(v___x_1527_, 2, v___x_1524_);
    return v___x_1527_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind_x3f___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1528_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x3f___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x3f___closed__3_once),
        _init_l_Lean_Parser_Attr_grind_x3f___closed__3,
    );
    v___x_1529_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_1530_ = l_Lean_Parser_Attr_grind_x3f___closed__1;
    v___x_1531_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1531_, 0, v___x_1530_);
    crate::leanh::lean_ctor_set(v___x_1531_, 1, v___x_1529_);
    crate::leanh::lean_ctor_set(v___x_1531_, 2, v___x_1528_);
    return v___x_1531_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind_x3f() -> *mut crate::leanh::LeanObject {
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1532_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x3f___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x3f___closed__4_once),
        _init_l_Lean_Parser_Attr_grind_x3f___closed__4,
    );
    return v___x_1532_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind_x21_x3f___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1542_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind___closed__4_once),
        _init_l_Lean_Parser_Attr_grind___closed__4,
    );
    v___x_1543_ = l_Lean_Parser_Attr_grind_x21_x3f___closed__2;
    v___x_1544_ = l_Lean_Parser_Attr_grindGen___closed__4;
    v___x_1545_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1545_, 0, v___x_1544_);
    crate::leanh::lean_ctor_set(v___x_1545_, 1, v___x_1543_);
    crate::leanh::lean_ctor_set(v___x_1545_, 2, v___x_1542_);
    return v___x_1545_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind_x21_x3f___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x21_x3f___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x21_x3f___closed__3_once),
        _init_l_Lean_Parser_Attr_grind_x21_x3f___closed__3,
    );
    v___x_1547_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_1548_ = l_Lean_Parser_Attr_grind_x21_x3f___closed__1;
    v___x_1549_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1549_, 0, v___x_1548_);
    crate::leanh::lean_ctor_set(v___x_1549_, 1, v___x_1547_);
    crate::leanh::lean_ctor_set(v___x_1549_, 2, v___x_1546_);
    return v___x_1549_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_grind_x21_x3f() -> *mut crate::leanh::LeanObject {
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1550_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x21_x3f___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_grind_x21_x3f___closed__4_once),
        _init_l_Lean_Parser_Attr_grind_x21_x3f___closed__4,
    );
    return v___x_1550_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Attr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Attr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Parser_Attr_grindNorm = _init_l_Lean_Parser_Attr_grindNorm();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Attr_grindNorm);
    l_Lean_Parser_Attr_grindMod = _init_l_Lean_Parser_Attr_grindMod();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Attr_grindMod);
    l_Lean_Parser_Attr_grind = _init_l_Lean_Parser_Attr_grind();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Attr_grind);
    l_Lean_Parser_Attr_grind_x21 = _init_l_Lean_Parser_Attr_grind_x21();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Attr_grind_x21);
    l_Lean_Parser_Attr_grind_x3f = _init_l_Lean_Parser_Attr_grind_x3f();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Attr_grind_x3f);
    l_Lean_Parser_Attr_grind_x21_x3f = _init_l_Lean_Parser_Attr_grind_x21_x3f();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Attr_grind_x21_x3f);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Attr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Attr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Attr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Grind_Attr(builtin);
}
