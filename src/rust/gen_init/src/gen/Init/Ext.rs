// Lean compiler output
// Module: Init.Ext
// Imports: Init.RCases
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
};
use crate::r#gen::Init::RCases::{initialize_Init_RCases, runtime_initialize_Init_RCases};
use crate::ffi::{lean_array_get_size, lean_nat_dec_eq};
pub static l_Lean_Parser_Attr_extIff___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [101, 120, 116, 73, 102, 102, 0],
    };
static mut l_Lean_Parser_Attr_extIff___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__1_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Parser_Attr_extIff___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__2_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Lean_Parser_Attr_extIff___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__3_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Parser_Attr_extIff___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_extIff___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__1_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_extIff___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_extIff___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__3_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_extIff___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17771787246881167207 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extIff___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__5_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Lean_Parser_Attr_extIff___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__5_value)
                as *mut crate::leanh::LeanObject,
            4024150434455327032 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extIff___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__7_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Lean_Parser_Attr_extIff___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__7_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extIff___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__9_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [40, 0],
    };
static mut l_Lean_Parser_Attr_extIff___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__10_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extIff___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__11_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [105, 102, 102, 0],
    };
static mut l_Lean_Parser_Attr_extIff___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__12_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__11_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extIff___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__13_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extIff___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__14_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [32, 58, 61, 32, 0],
    };
static mut l_Lean_Parser_Attr_extIff___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__15_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extIff___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__16_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__13_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extIff___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__17_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Parser_Attr_extIff___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__18_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__17_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extIff___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__19_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__16_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extIff___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__20_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [41, 0],
    };
static mut l_Lean_Parser_Attr_extIff___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__21_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__20_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extIff___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__22_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__19_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__21_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extIff___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__23_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__22_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extIff___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extIff___closed__24_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__23_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extIff___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Attr_extIff: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extFlat___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [101, 120, 116, 70, 108, 97, 116, 0],
    };
static mut l_Lean_Parser_Attr_extFlat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_extFlat___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__1_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_extFlat___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_extFlat___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__3_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_extFlat___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            1601808699437151451 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extFlat___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extFlat___closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [102, 108, 97, 116, 0],
    };
static mut l_Lean_Parser_Attr_extFlat___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extFlat___closed__3_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extFlat___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extFlat___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extFlat___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extFlat___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extFlat___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extFlat___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extFlat___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extFlat___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__21_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extFlat___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extFlat___closed__8_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extFlat___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extFlat___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extFlat___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Attr_extFlat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_ext___closed__0_value: crate::leanh::LeanStringObject<4> =
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
static mut l_Lean_Parser_Attr_ext___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_ext___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__1_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_ext___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Parser_Attr_ext___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__3_value)
                as *mut crate::leanh::LeanObject,
            4584992172905639687 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_Attr_ext___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6815193930280145701 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_ext___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_ext___closed__2_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__0_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_ext___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_ext___closed__3_value: crate::leanh::LeanStringObject<9> =
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
static mut l_Lean_Parser_Attr_ext___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_ext___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__3_value)
                as *mut crate::leanh::LeanObject,
            18170484695678750185 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_ext___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_ext___closed__5_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Lean_Parser_Attr_ext___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_ext___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__5_value)
                as *mut crate::leanh::LeanObject,
            17761616517784022991 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_ext___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_ext___closed__7_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_ext___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_ext___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__24_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_ext___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_ext___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_ext___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_ext___closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_ext___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_ext___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extFlat___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_ext___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_ext___closed__12_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_ext___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_ext___closed__13_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_ext___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_ext___closed__14_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Parser_Attr_ext___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_ext___closed__15_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__14_value)
                as *mut crate::leanh::LeanObject,
            17836958171642591098 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_ext___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_ext___closed__16_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__15_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_ext___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_ext___closed__17_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_ext___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_ext___closed__18_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__17_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_ext___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_ext___closed__19_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__13_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_ext___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_ext___closed__20_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_ext___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__20_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_Attr_ext: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [69, 108, 97, 98, 0],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__1_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__2_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [69, 120, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Ext_ext___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__1_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Ext_ext___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11510100434945111860 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Ext_ext___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__1_value)
                as *mut crate::leanh::LeanObject,
            12733524109236233889 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Ext_ext___closed__3_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__3_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__2_value)
                as *mut crate::leanh::LeanObject,
            3368083297340442161 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Ext_ext___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__3_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5275990690386282739 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__4_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [109, 97, 110, 121, 0],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__4_value)
                as *mut crate::leanh::LeanObject,
            2302572775315350313 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__6_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [99, 111, 108, 71, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__6_value)
                as *mut crate::leanh::LeanObject,
            17597206043415342265 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__8_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__10_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [114, 105, 110, 116, 114, 111, 80, 97, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__10_value)
                as *mut crate::leanh::LeanObject,
            1409078044207596393 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__12_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__11_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__13_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__14_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__15_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__16_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [32, 58, 32, 0],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__17_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__18_value: crate::leanh::LeanStringObject<4> =
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
static mut l_Lean_Elab_Tactic_Ext_ext___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__19_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__18_value)
                as *mut crate::leanh::LeanObject,
            6110315075117401315 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__20_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__21_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__17_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__20_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__22_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_ext___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__21_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__23_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__22_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_ext___closed__24_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__3_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__23_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Ext_ext___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Ext_ext: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__0_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
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
        97, 112, 112, 108, 121, 69, 120, 116, 84, 104, 101, 111, 114, 101, 109, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__1_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11510100434945111860 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__1_value)
            as *mut crate::leanh::LeanObject,
        12733524109236233889 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__2_value)
            as *mut crate::leanh::LeanObject,
        3368083297340442161 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7693090546407419771 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__2_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        97, 112, 112, 108, 121, 95, 101, 120, 116, 95, 116, 104, 101, 111, 114, 101, 109, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__3_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__2_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__4_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Ext_applyExtTheorem: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__0_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [116, 97, 99, 116, 105, 99, 69, 120, 116, 49, 95, 95, 95, 0],
};
static mut l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__1_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11510100434945111860 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__1_value)
            as *mut crate::leanh::LeanObject,
        12733524109236233889 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__2_value)
            as *mut crate::leanh::LeanObject,
        3368083297340442161 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        2532130838934482863 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__2_value:
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
    m_data: [101, 120, 116, 49, 0],
};
static mut l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__2_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__14_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Ext_tacticExt1______: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__0_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [116, 97, 99, 116, 105, 99, 95, 60, 59, 62, 95, 0]};
static mut l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__2_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__0_value) as *mut crate::leanh::LeanObject,12695378809397736991 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [60, 59, 62, 0]};
static mut l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__3_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 105, 110, 116, 114, 111, 0]};
static mut l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__2_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__3_value) as *mut crate::leanh::LeanObject,10592081902191181482 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__5_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__8_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 116, 114, 111, 115, 0]};
static mut l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__8_value) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_extIff___closed__2_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext_ext___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__9_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__8_value) as *mut crate::leanh::LeanObject,3278676588586250010 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__9_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_594_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_594_;
}
pub unsafe fn l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1(
    mut v_x_601_: *mut crate::leanh::LeanObject,
    mut v_a_602_: *mut crate::leanh::LeanObject,
    mut v_a_603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: u8 = 0;
    v___x_604_ = l_Lean_Elab_Tactic_Ext_tacticExt1_______00__closed__1;
    crate::leanh::lean_inc(v_x_601_);
    v___x_605_ = l_Lean_Syntax_isOfKind(v_x_601_, v___x_604_);
    if v___x_605_ == 0 {
        let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_601_);
        v___x_606_ = crate::leanh::lean_box(1);
        v___x_607_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_607_, 0, v___x_606_);
        crate::leanh::lean_ctor_set(v___x_607_, 1, v_a_603_);
        return v___x_607_;
    } else {
        let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_xs_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_613_: u8 = 0;
        v___x_608_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_609_ = l_Lean_Syntax_getArg(v_x_601_, v___x_608_);
        crate::leanh::lean_dec(v_x_601_);
        v_xs_610_ = l_Lean_Syntax_getArgs(v___x_609_);
        crate::leanh::lean_dec(v___x_609_);
        v___x_611_ = lean_array_get_size(v_xs_610_);
        v___x_612_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_613_ = lean_nat_dec_eq(v___x_611_, v___x_612_);
        if v___x_613_ == 0 {
            let mut v_ref_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_ref_614_ = crate::leanh::lean_ctor_get(v_a_602_, 5);
            v___x_615_ = l_Lean_SourceInfo_fromRef(v_ref_614_, v___x_613_);
            v___x_616_ = l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__1;
            v___x_617_ = l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1;
            v___x_618_ = l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__2;
            crate::leanh::lean_inc_n(v___x_615_, 7);
            v___x_619_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_619_, 0, v___x_615_);
            crate::leanh::lean_ctor_set(v___x_619_, 1, v___x_618_);
            v___x_620_ = l_Lean_Syntax_node1(v___x_615_, v___x_617_, v___x_619_);
            v___x_621_ = l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__2;
            v___x_622_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_622_, 0, v___x_615_);
            crate::leanh::lean_ctor_set(v___x_622_, 1, v___x_621_);
            v___x_623_ = l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__3;
            v___x_624_ = l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__4;
            v___x_625_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_625_, 0, v___x_615_);
            crate::leanh::lean_ctor_set(v___x_625_, 1, v___x_623_);
            v___x_626_ = l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__6;
            v___x_627_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__7_once), _init_l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__7);
            v___x_628_ = l_Array_append___redArg(v___x_627_, v_xs_610_);
            crate::leanh::lean_dec_ref(v_xs_610_);
            v___x_629_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_629_, 0, v___x_615_);
            crate::leanh::lean_ctor_set(v___x_629_, 1, v___x_626_);
            crate::leanh::lean_ctor_set(v___x_629_, 2, v___x_628_);
            v___x_630_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_630_, 0, v___x_615_);
            crate::leanh::lean_ctor_set(v___x_630_, 1, v___x_626_);
            crate::leanh::lean_ctor_set(v___x_630_, 2, v___x_627_);
            v___x_631_ =
                l_Lean_Syntax_node3(v___x_615_, v___x_624_, v___x_625_, v___x_629_, v___x_630_);
            v___x_632_ =
                l_Lean_Syntax_node3(v___x_615_, v___x_616_, v___x_620_, v___x_622_, v___x_631_);
            v___x_633_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_633_, 0, v___x_632_);
            crate::leanh::lean_ctor_set(v___x_633_, 1, v_a_603_);
            return v___x_633_;
        } else {
            let mut v_ref_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_635_: u8 = 0;
            let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_xs_610_);
            v_ref_634_ = crate::leanh::lean_ctor_get(v_a_602_, 5);
            v___x_635_ = 0;
            v___x_636_ = l_Lean_SourceInfo_fromRef(v_ref_634_, v___x_635_);
            v___x_637_ = l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__1;
            v___x_638_ = l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__1;
            v___x_639_ = l_Lean_Elab_Tactic_Ext_applyExtTheorem___closed__2;
            crate::leanh::lean_inc_n(v___x_636_, 6);
            v___x_640_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_640_, 0, v___x_636_);
            crate::leanh::lean_ctor_set(v___x_640_, 1, v___x_639_);
            v___x_641_ = l_Lean_Syntax_node1(v___x_636_, v___x_638_, v___x_640_);
            v___x_642_ = l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__2;
            v___x_643_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_643_, 0, v___x_636_);
            crate::leanh::lean_ctor_set(v___x_643_, 1, v___x_642_);
            v___x_644_ = l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__8;
            v___x_645_ = l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__9;
            v___x_646_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_646_, 0, v___x_636_);
            crate::leanh::lean_ctor_set(v___x_646_, 1, v___x_644_);
            v___x_647_ = l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__6;
            v___x_648_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__7_once), _init_l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___closed__7);
            v___x_649_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_649_, 0, v___x_636_);
            crate::leanh::lean_ctor_set(v___x_649_, 1, v___x_647_);
            crate::leanh::lean_ctor_set(v___x_649_, 2, v___x_648_);
            v___x_650_ = l_Lean_Syntax_node2(v___x_636_, v___x_645_, v___x_646_, v___x_649_);
            v___x_651_ =
                l_Lean_Syntax_node3(v___x_636_, v___x_637_, v___x_641_, v___x_643_, v___x_650_);
            v___x_652_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_652_, 0, v___x_651_);
            crate::leanh::lean_ctor_set(v___x_652_, 1, v_a_603_);
            return v___x_652_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1___boxed(
    mut v_x_653_: *mut crate::leanh::LeanObject,
    mut v_a_654_: *mut crate::leanh::LeanObject,
    mut v_a_655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_656_ = l_Lean_Elab_Tactic_Ext___aux__Init__Ext______macroRules__Lean__Elab__Tactic__Ext__tacticExt1________1(v_x_653_, v_a_654_, v_a_655_);
    crate::leanh::lean_dec_ref(v_a_654_);
    return v_res_656_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Ext(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_RCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Ext(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Ext(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_RCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Ext(builtin);
}
