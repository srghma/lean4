// Lean compiler output
// Module: Init.Data.List.Notation
// Imports: Init.Grind.Tactics Init.Notation
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::Notation::{initialize_Init_Notation, runtime_initialize_Init_Notation};
use crate::r#gen::Init::Prelude::{
    l_Array_appendCore___redArg, l_Array_mkArray0, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2,
    l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_node2, l_Lean_Syntax_node5, l_Lean_addMacroScope,
    l_String_toRawSubstring_x27,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_borrowed, lean_array_get_size, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_mod,
    lean_nat_sub,
};
pub static l_term_x5b___x5d___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [116, 101, 114, 109, 91, 95, 93, 0],
    };
static mut l_term_x5b___x5d___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_term_x5b___x5d___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_x5b___x5d___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11666683425613976406 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_x5b___x5d___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_term_x5b___x5d___closed__2_value: crate::leanh::LeanStringObject<8> =
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
static mut l_term_x5b___x5d___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_term_x5b___x5d___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_x5b___x5d___closed__2_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_x5b___x5d___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_term_x5b___x5d___closed__4_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [91, 0],
    };
static mut l_term_x5b___x5d___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_term_x5b___x5d___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_term_x5b___x5d___closed__4_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_term_x5b___x5d___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_term_x5b___x5d___closed__6_value: crate::leanh::LeanStringObject<16> =
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
            119, 105, 116, 104, 111, 117, 116, 80, 111, 115, 105, 116, 105, 111, 110, 0,
        ],
    };
static mut l_term_x5b___x5d___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_term_x5b___x5d___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_x5b___x5d___closed__6_value)
                as *mut crate::leanh::LeanObject,
            1164644006045091397 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_x5b___x5d___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_term_x5b___x5d___closed__8_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_term_x5b___x5d___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_term_x5b___x5d___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_x5b___x5d___closed__8_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_x5b___x5d___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_term_x5b___x5d___closed__10_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_term_x5b___x5d___closed__9_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_x5b___x5d___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_term_x5b___x5d___closed__11_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [44, 0],
    };
static mut l_term_x5b___x5d___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_term_x5b___x5d___closed__12_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [44, 32, 0],
    };
static mut l_term_x5b___x5d___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_term_x5b___x5d___closed__13_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_term_x5b___x5d___closed__12_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_term_x5b___x5d___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_term_x5b___x5d___closed__14_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 10,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_x5b___x5d___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__11_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__13_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_x5b___x5d___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_term_x5b___x5d___closed__15_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_term_x5b___x5d___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_x5b___x5d___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_term_x5b___x5d___closed__16_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_x5b___x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_x5b___x5d___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_term_x5b___x5d___closed__17_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [93, 0],
    };
static mut l_term_x5b___x5d___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_term_x5b___x5d___closed__18_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_term_x5b___x5d___closed__17_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_term_x5b___x5d___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_term_x5b___x5d___closed__19_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_x5b___x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__16_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_x5b___x5d___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l_term_x5b___x5d___closed__20_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_x5b___x5d___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_x5b___x5d___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__20_value) as *mut crate::leanh::LeanObject;
pub static mut l_term_x5b___x5d: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [116, 101, 114, 109, 37, 91, 95, 124, 95, 93, 0],
    };
static mut l_term_x25_x5b___x7c___x5d___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11736852788046959995 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_x25_x5b___x7c___x5d___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__2_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [37, 91, 0],
    };
static mut l_term_x25_x5b___x7c___x5d___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_x25_x5b___x7c___x5d___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__4_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [32, 124, 32, 0],
    };
static mut l_term_x25_x5b___x7c___x5d___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__5_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_x25_x5b___x7c___x5d___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_x5b___x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__14_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_x25_x5b___x7c___x5d___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_x5b___x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_x25_x5b___x7c___x5d___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__8_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_term_x5b___x5d___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_x25_x5b___x7c___x5d___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_x5b___x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_x25_x5b___x7c___x5d___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_x5b___x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_x25_x5b___x7c___x5d___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_x25_x5b___x7c___x5d___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_term_x25_x5b___x7c___x5d: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__3_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__5_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [76, 105, 115, 116, 46, 99, 111, 110, 115, 0]};
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 105, 115, 116, 0]};
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__8_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 110, 115, 0]};
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__8_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__7_value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__8_value) as *mut crate::leanh::LeanObject,8614124190858717794 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__10_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__11_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__12_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__11_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__13_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__10_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__12_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__14_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__14_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__15_value) as *mut crate::leanh::LeanObject;
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__2_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [76, 105, 115, 116, 46, 110, 105, 108, 0]};
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__4_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 105, 108, 0]};
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__4_value) as *mut crate::leanh::LeanObject;
static l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__7_value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__4_value) as *mut crate::leanh::LeanObject,18135193680607614554 as *mut crate::leanh::LeanObject] };
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__7_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__8_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__7_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__6_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__8_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_311_ = l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__5;
    v___x_312_ = l_String_toRawSubstring_x27(v___x_311_);
    return v___x_312_;
}
pub unsafe fn l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit(
    mut v_elems_332_: *mut crate::leanh::LeanObject,
    mut v_i_333_: *mut crate::leanh::LeanObject,
    mut v_skip_334_: u8,
    mut v_result_335_: *mut crate::leanh::LeanObject,
    mut v_a_336_: *mut crate::leanh::LeanObject,
    mut v_a_337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_339_: u8 = 0;
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_338_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_339_ = lean_nat_dec_eq(v_i_333_, v_zero_338_);
                if v_isZero_339_ == 1 {
                    crate::leanh::lean_dec(v_i_333_);
                    v___x_340_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_340_, 0, v_result_335_);
                    crate::leanh::lean_ctor_set(v___x_340_, 1, v_a_337_);
                    return v___x_340_;
                } else {
                    v_one_341_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_342_ = lean_nat_sub(v_i_333_, v_one_341_);
                    crate::leanh::lean_dec(v_i_333_);
                    if v_skip_334_ == 0 {
                        v_quotContext_343_ = crate::leanh::lean_ctor_get(v_a_336_, 1);
                        v_currMacroScope_344_ = crate::leanh::lean_ctor_get(v_a_336_, 2);
                        v_ref_345_ = crate::leanh::lean_ctor_get(v_a_336_, 5);
                        v___x_346_ = crate::leanh::lean_box(0);
                        v___x_347_ = l_Lean_SourceInfo_fromRef(v_ref_345_, v_skip_334_);
                        v___x_348_ = l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4;
                        v___x_349_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__6_once), _init_l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__6);
                        v___x_350_ = l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9;
                        crate::leanh::lean_inc(v_currMacroScope_344_);
                        crate::leanh::lean_inc(v_quotContext_343_);
                        v___x_351_ = l_Lean_addMacroScope(
                            v_quotContext_343_,
                            v___x_350_,
                            v_currMacroScope_344_,
                        );
                        v___x_352_ = l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__13;
                        crate::leanh::lean_inc_n(v___x_347_, 2);
                        v___x_353_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_353_, 0, v___x_347_);
                        crate::leanh::lean_ctor_set(v___x_353_, 1, v___x_349_);
                        crate::leanh::lean_ctor_set(v___x_353_, 2, v___x_351_);
                        crate::leanh::lean_ctor_set(v___x_353_, 3, v___x_352_);
                        v___x_354_ = l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__15;
                        v___x_355_ = lean_array_get_borrowed(v___x_346_, v_elems_332_, v_n_342_);
                        crate::leanh::lean_inc(v___x_355_);
                        v___x_356_ =
                            l_Lean_Syntax_node2(v___x_347_, v___x_354_, v___x_355_, v_result_335_);
                        v___x_357_ =
                            l_Lean_Syntax_node2(v___x_347_, v___x_348_, v___x_353_, v___x_356_);
                        v___x_358_ = 1;
                        v_i_333_ = v_n_342_;
                        v_skip_334_ = v___x_358_;
                        v_result_335_ = v___x_357_;
                        state = 0;
                        continue;
                    } else {
                        v_i_333_ = v_n_342_;
                        v_skip_334_ = v_isZero_339_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___boxed(
    mut v_elems_361_: *mut crate::leanh::LeanObject,
    mut v_i_362_: *mut crate::leanh::LeanObject,
    mut v_skip_363_: *mut crate::leanh::LeanObject,
    mut v_result_364_: *mut crate::leanh::LeanObject,
    mut v_a_365_: *mut crate::leanh::LeanObject,
    mut v_a_366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skip_boxed_367_: u8 = 0;
    let mut v_res_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skip_boxed_367_ = (crate::leanh::lean_unbox(v_skip_363_) as u8);
    v_res_368_ = l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit(v_elems_361_, v_i_362_, v_skip_boxed_367_, v_result_364_, v_a_365_, v_a_366_);
    crate::leanh::lean_dec_ref(v_a_365_);
    crate::leanh::lean_dec_ref(v_elems_361_);
    return v_res_368_;
}
pub unsafe fn _init_l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_369_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_369_;
}
pub unsafe fn _init_l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_372_ =
        l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__2;
    v___x_373_ = l_String_toRawSubstring_x27(v___x_372_);
    return v___x_373_;
}
pub unsafe fn l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1(
    mut v_x_389_: *mut crate::leanh::LeanObject,
    mut v_a_390_: *mut crate::leanh::LeanObject,
    mut v_a_391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: u8 = 0;
    v___x_392_ = l_term_x5b___x5d___closed__1;
    crate::leanh::lean_inc(v_x_389_);
    v___x_393_ = l_Lean_Syntax_isOfKind(v_x_389_, v___x_392_);
    if v___x_393_ == 0 {
        let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_389_);
        v___x_394_ = crate::leanh::lean_box(1);
        v___x_395_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_395_, 0, v___x_394_);
        crate::leanh::lean_ctor_set(v___x_395_, 1, v_a_391_);
        return v___x_395_;
    } else {
        let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_elems_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_size_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_401_: u8 = 0;
        v___x_396_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_397_ = l_Lean_Syntax_getArg(v_x_389_, v___x_396_);
        crate::leanh::lean_dec(v_x_389_);
        v_elems_398_ = l_Lean_Syntax_getArgs(v___x_397_);
        crate::leanh::lean_dec(v___x_397_);
        v_size_399_ = lean_array_get_size(v_elems_398_);
        v___x_400_ = crate::leanh::lean_unsigned_to_nat(64);
        v___x_401_ = lean_nat_dec_lt(v_size_399_, v___x_400_);
        if v___x_401_ == 0 {
            let mut v_quotContext_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ref_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_quotContext_402_ = crate::leanh::lean_ctor_get(v_a_390_, 1);
            v_currMacroScope_403_ = crate::leanh::lean_ctor_get(v_a_390_, 2);
            v_ref_404_ = crate::leanh::lean_ctor_get(v_a_390_, 5);
            v___x_405_ = l_Lean_SourceInfo_fromRef(v_ref_404_, v___x_401_);
            v___x_406_ = l_term_x25_x5b___x7c___x5d___closed__1;
            v___x_407_ = l_term_x25_x5b___x7c___x5d___closed__2;
            crate::leanh::lean_inc_n(v___x_405_, 5);
            v___x_408_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_408_, 0, v___x_405_);
            crate::leanh::lean_ctor_set(v___x_408_, 1, v___x_407_);
            v___x_409_ = l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__15;
            v___x_410_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__0), core::ptr::addr_of_mut!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__0_once), _init_l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__0);
            v___x_411_ = l_Array_appendCore___redArg(v___x_410_, v_elems_398_);
            crate::leanh::lean_dec_ref(v_elems_398_);
            v___x_412_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_412_, 0, v___x_405_);
            crate::leanh::lean_ctor_set(v___x_412_, 1, v___x_409_);
            crate::leanh::lean_ctor_set(v___x_412_, 2, v___x_411_);
            v___x_413_ = l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__1;
            v___x_414_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_414_, 0, v___x_405_);
            crate::leanh::lean_ctor_set(v___x_414_, 1, v___x_413_);
            v___x_415_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3), core::ptr::addr_of_mut!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3_once), _init_l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3);
            v___x_416_ = l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5;
            crate::leanh::lean_inc(v_currMacroScope_403_);
            crate::leanh::lean_inc(v_quotContext_402_);
            v___x_417_ =
                l_Lean_addMacroScope(v_quotContext_402_, v___x_416_, v_currMacroScope_403_);
            v___x_418_ = l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__9;
            v___x_419_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_419_, 0, v___x_405_);
            crate::leanh::lean_ctor_set(v___x_419_, 1, v___x_415_);
            crate::leanh::lean_ctor_set(v___x_419_, 2, v___x_417_);
            crate::leanh::lean_ctor_set(v___x_419_, 3, v___x_418_);
            v___x_420_ = l_term_x5b___x5d___closed__17;
            v___x_421_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_421_, 0, v___x_405_);
            crate::leanh::lean_ctor_set(v___x_421_, 1, v___x_420_);
            v___x_422_ = l_Lean_Syntax_node5(
                v___x_405_, v___x_406_, v___x_408_, v___x_412_, v___x_414_, v___x_419_, v___x_421_,
            );
            v___x_423_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_423_, 0, v___x_422_);
            crate::leanh::lean_ctor_set(v___x_423_, 1, v_a_391_);
            return v___x_423_;
        } else {
            let mut v_quotContext_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ref_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_429_: u8 = 0;
            let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_437_: u8 = 0;
            let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_quotContext_424_ = crate::leanh::lean_ctor_get(v_a_390_, 1);
            v_currMacroScope_425_ = crate::leanh::lean_ctor_get(v_a_390_, 2);
            v_ref_426_ = crate::leanh::lean_ctor_get(v_a_390_, 5);
            v___x_427_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_428_ = crate::leanh::lean_unsigned_to_nat(2);
            v___x_429_ = 0;
            v___x_430_ = l_Lean_SourceInfo_fromRef(v_ref_426_, v___x_429_);
            v___x_431_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3), core::ptr::addr_of_mut!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3_once), _init_l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3);
            v___x_432_ = l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5;
            crate::leanh::lean_inc(v_currMacroScope_425_);
            crate::leanh::lean_inc(v_quotContext_424_);
            v___x_433_ =
                l_Lean_addMacroScope(v_quotContext_424_, v___x_432_, v_currMacroScope_425_);
            v___x_434_ = l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__9;
            v___x_435_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_435_, 0, v___x_430_);
            crate::leanh::lean_ctor_set(v___x_435_, 1, v___x_431_);
            crate::leanh::lean_ctor_set(v___x_435_, 2, v___x_433_);
            crate::leanh::lean_ctor_set(v___x_435_, 3, v___x_434_);
            v___x_436_ = lean_nat_mod(v_size_399_, v___x_428_);
            v___x_437_ = lean_nat_dec_eq(v___x_436_, v___x_427_);
            crate::leanh::lean_dec(v___x_436_);
            v___x_438_ = l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit(v_elems_398_, v_size_399_, v___x_437_, v___x_435_, v_a_390_, v_a_391_);
            crate::leanh::lean_dec_ref(v_elems_398_);
            return v___x_438_;
        }
    }
}
pub unsafe fn l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___boxed(
    mut v_x_439_: *mut crate::leanh::LeanObject,
    mut v_a_440_: *mut crate::leanh::LeanObject,
    mut v_a_441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_442_ = l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1(
        v_x_439_, v_a_440_, v_a_441_,
    );
    crate::leanh::lean_dec_ref(v_a_440_);
    return v_res_442_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Notation(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Notation(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Notation(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_Notation(builtin);
}
