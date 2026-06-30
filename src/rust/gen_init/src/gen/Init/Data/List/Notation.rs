// Lean compiler output
// Module: Init.Data.List.Notation
// Imports: Init.Grind.Tactics Init.Notation
use crate::ffi::{
    lean_array_get_borrowed, lean_array_get_size, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_mod,
    lean_nat_sub,
};
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::Notation::{initialize_Init_Notation, runtime_initialize_Init_Notation};
use crate::r#gen::Init::Prelude::{
    l_Array_appendCore___redArg, l_Array_mkArray0, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node2, l_Lean_Syntax_node5,
    l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
pub static l_term_x5b___x5d___closed__0_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_term_x5b___x5d___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__0_value) as *mut leanh::LeanObject;
pub static l_term_x5b___x5d___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__0_value)
                as *mut leanh::LeanObject,
            11666683425613976406 as *mut leanh::LeanObject,
        ],
    };
static mut l_term_x5b___x5d___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__1_value) as *mut leanh::LeanObject;
pub static l_term_x5b___x5d___closed__2_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_term_x5b___x5d___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__2_value) as *mut leanh::LeanObject;
pub static l_term_x5b___x5d___closed__3_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__2_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_term_x5b___x5d___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__3_value) as *mut leanh::LeanObject;
pub static l_term_x5b___x5d___closed__4_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_term_x5b___x5d___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__4_value) as *mut leanh::LeanObject;
pub static l_term_x5b___x5d___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_term_x5b___x5d___closed__4_value)
            as *mut leanh::LeanObject],
    };
static mut l_term_x5b___x5d___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__5_value) as *mut leanh::LeanObject;
pub static l_term_x5b___x5d___closed__6_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_term_x5b___x5d___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__6_value) as *mut leanh::LeanObject;
pub static l_term_x5b___x5d___closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__6_value)
                as *mut leanh::LeanObject,
            1164644006045091397 as *mut leanh::LeanObject,
        ],
    };
static mut l_term_x5b___x5d___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__7_value) as *mut leanh::LeanObject;
pub static l_term_x5b___x5d___closed__8_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_term_x5b___x5d___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__8_value) as *mut leanh::LeanObject;
pub static l_term_x5b___x5d___closed__9_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__8_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_term_x5b___x5d___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__9_value) as *mut leanh::LeanObject;
pub static l_term_x5b___x5d___closed__10_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_x5b___x5d___closed__9_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_term_x5b___x5d___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__10_value) as *mut leanh::LeanObject;
pub static l_term_x5b___x5d___closed__11_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_term_x5b___x5d___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__11_value) as *mut leanh::LeanObject;
pub static l_term_x5b___x5d___closed__12_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_term_x5b___x5d___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__12_value) as *mut leanh::LeanObject;
pub static l_term_x5b___x5d___closed__13_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_term_x5b___x5d___closed__12_value)
            as *mut leanh::LeanObject],
    };
static mut l_term_x5b___x5d___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__13_value) as *mut leanh::LeanObject;
pub static l_term_x5b___x5d___closed__14_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 10,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_x5b___x5d___closed__10_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__11_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__13_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_term_x5b___x5d___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__14_value) as *mut leanh::LeanObject;
pub static l_term_x5b___x5d___closed__15_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_x5b___x5d___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_x5b___x5d___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__15_value) as *mut leanh::LeanObject;
pub static l_term_x5b___x5d___closed__16_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_x5b___x5d___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_x5b___x5d___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__16_value) as *mut leanh::LeanObject;
pub static l_term_x5b___x5d___closed__17_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_term_x5b___x5d___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__17_value) as *mut leanh::LeanObject;
pub static l_term_x5b___x5d___closed__18_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_term_x5b___x5d___closed__17_value)
            as *mut leanh::LeanObject],
    };
static mut l_term_x5b___x5d___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__18_value) as *mut leanh::LeanObject;
pub static l_term_x5b___x5d___closed__19_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_x5b___x5d___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__16_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__18_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_x5b___x5d___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__19_value) as *mut leanh::LeanObject;
pub static l_term_x5b___x5d___closed__20_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_x5b___x5d___closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__19_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_x5b___x5d___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__20_value) as *mut leanh::LeanObject;
pub static mut l_term_x5b___x5d: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x5b___x5d___closed__20_value) as *mut leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__0_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_term_x25_x5b___x7c___x5d___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__0_value)
                as *mut leanh::LeanObject,
            11736852788046959995 as *mut leanh::LeanObject,
        ],
    };
static mut l_term_x25_x5b___x7c___x5d___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__2_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_term_x25_x5b___x7c___x5d___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_x25_x5b___x7c___x5d___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__4_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_term_x25_x5b___x7c___x5d___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_x25_x5b___x7c___x5d___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__6_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_x5b___x5d___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__14_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_x25_x5b___x7c___x5d___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_x5b___x5d___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_x25_x5b___x7c___x5d___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__8_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_x5b___x5d___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_x25_x5b___x7c___x5d___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__9_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_x5b___x5d___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_x25_x5b___x7c___x5d___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__10_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_x5b___x5d___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x5b___x5d___closed__18_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_x25_x5b___x7c___x5d___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_term_x25_x5b___x7c___x5d___closed__11_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_x25_x5b___x7c___x5d___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__11_value)
        as *mut leanh::LeanObject;
pub static mut l_term_x25_x5b___x7c___x5d: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_x25_x5b___x7c___x5d___closed__11_value)
        as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__3_value) as *mut leanh::LeanObject;
static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__3_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__5_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [76, 105, 115, 116, 46, 99, 111, 110, 115, 0]};
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__7_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 105, 115, 116, 0]};
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__8_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 110, 115, 0]};
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__8_value) as *mut leanh::LeanObject;
static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__7_value) as *mut leanh::LeanObject,9582258842178272501 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__8_value) as *mut leanh::LeanObject,8614124190858717794 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__10_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__11_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__12_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__11_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__13_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__10_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__12_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__14_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__14_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__14_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__15_value) as *mut leanh::LeanObject;
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__2_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [76, 105, 115, 116, 46, 110, 105, 108, 0]};
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__4_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 105, 108, 0]};
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__4_value) as *mut leanh::LeanObject;
static l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__7_value) as *mut leanh::LeanObject,9582258842178272501 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__4_value) as *mut leanh::LeanObject,18135193680607614554 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__7_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5_value) as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__8_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__7_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__9_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__6_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__8_value) as *mut leanh::LeanObject] };
static mut l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__9_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_311_ = l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__5;
    v___x_312_ = l_String_toRawSubstring_x27(v___x_311_);
    return v___x_312_;
}
pub unsafe fn l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit(
    mut v_elems_332_: *mut leanh::LeanObject,
    mut v_i_333_: *mut leanh::LeanObject,
    mut v_skip_334_: u8,
    mut v_result_335_: *mut leanh::LeanObject,
    mut v_a_336_: *mut leanh::LeanObject,
    mut v_a_337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_339_: u8 = 0;
    let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_338_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_339_ = lean_nat_dec_eq(v_i_333_, v_zero_338_);
                if v_isZero_339_ == 1 {
                    leanh::lean_dec(v_i_333_);
                    v___x_340_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_340_, 0, v_result_335_);
                    leanh::lean_ctor_set(v___x_340_, 1, v_a_337_);
                    return v___x_340_;
                } else {
                    v_one_341_ = leanh::lean_unsigned_to_nat(1);
                    v_n_342_ = lean_nat_sub(v_i_333_, v_one_341_);
                    leanh::lean_dec(v_i_333_);
                    if v_skip_334_ == 0 {
                        v_quotContext_343_ = leanh::lean_ctor_get(v_a_336_, 1);
                        v_currMacroScope_344_ = leanh::lean_ctor_get(v_a_336_, 2);
                        v_ref_345_ = leanh::lean_ctor_get(v_a_336_, 5);
                        v___x_346_ = leanh::lean_box(0);
                        v___x_347_ = l_Lean_SourceInfo_fromRef(v_ref_345_, v_skip_334_);
                        v___x_348_ = l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__4;
                        v___x_349_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__6_once), _init_l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__6);
                        v___x_350_ = l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__9;
                        leanh::lean_inc(v_currMacroScope_344_);
                        leanh::lean_inc(v_quotContext_343_);
                        v___x_351_ = l_Lean_addMacroScope(
                            v_quotContext_343_,
                            v___x_350_,
                            v_currMacroScope_344_,
                        );
                        v___x_352_ = l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__13;
                        leanh::lean_inc_n(v___x_347_, 2);
                        v___x_353_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                        leanh::lean_ctor_set(v___x_353_, 0, v___x_347_);
                        leanh::lean_ctor_set(v___x_353_, 1, v___x_349_);
                        leanh::lean_ctor_set(v___x_353_, 2, v___x_351_);
                        leanh::lean_ctor_set(v___x_353_, 3, v___x_352_);
                        v___x_354_ = l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__15;
                        v___x_355_ = lean_array_get_borrowed(v___x_346_, v_elems_332_, v_n_342_);
                        leanh::lean_inc(v___x_355_);
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
    mut v_elems_361_: *mut leanh::LeanObject,
    mut v_i_362_: *mut leanh::LeanObject,
    mut v_skip_363_: *mut leanh::LeanObject,
    mut v_result_364_: *mut leanh::LeanObject,
    mut v_a_365_: *mut leanh::LeanObject,
    mut v_a_366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skip_boxed_367_: u8 = 0;
    let mut v_res_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skip_boxed_367_ = (leanh::lean_unbox(v_skip_363_) as u8);
    v_res_368_ = l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit(v_elems_361_, v_i_362_, v_skip_boxed_367_, v_result_364_, v_a_365_, v_a_366_);
    leanh::lean_dec_ref(v_a_365_);
    leanh::lean_dec_ref(v_elems_361_);
    return v_res_368_;
}
pub unsafe fn _init_l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_369_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_369_;
}
pub unsafe fn _init_l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_372_ =
        l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__2;
    v___x_373_ = l_String_toRawSubstring_x27(v___x_372_);
    return v___x_373_;
}
pub unsafe fn l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1(
    mut v_x_389_: *mut leanh::LeanObject,
    mut v_a_390_: *mut leanh::LeanObject,
    mut v_a_391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: u8 = 0;
    v___x_392_ = l_term_x5b___x5d___closed__1;
    leanh::lean_inc(v_x_389_);
    v___x_393_ = l_Lean_Syntax_isOfKind(v_x_389_, v___x_392_);
    if v___x_393_ == 0 {
        let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_389_);
        v___x_394_ = leanh::lean_box(1);
        v___x_395_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_395_, 0, v___x_394_);
        leanh::lean_ctor_set(v___x_395_, 1, v_a_391_);
        return v___x_395_;
    } else {
        let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_elems_398_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_size_399_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_401_: u8 = 0;
        v___x_396_ = leanh::lean_unsigned_to_nat(1);
        v___x_397_ = l_Lean_Syntax_getArg(v_x_389_, v___x_396_);
        leanh::lean_dec(v_x_389_);
        v_elems_398_ = l_Lean_Syntax_getArgs(v___x_397_);
        leanh::lean_dec(v___x_397_);
        v_size_399_ = lean_array_get_size(v_elems_398_);
        v___x_400_ = leanh::lean_unsigned_to_nat(64);
        v___x_401_ = lean_nat_dec_lt(v_size_399_, v___x_400_);
        if v___x_401_ == 0 {
            let mut v_quotContext_402_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_403_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_ref_404_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_quotContext_402_ = leanh::lean_ctor_get(v_a_390_, 1);
            v_currMacroScope_403_ = leanh::lean_ctor_get(v_a_390_, 2);
            v_ref_404_ = leanh::lean_ctor_get(v_a_390_, 5);
            v___x_405_ = l_Lean_SourceInfo_fromRef(v_ref_404_, v___x_401_);
            v___x_406_ = l_term_x25_x5b___x7c___x5d___closed__1;
            v___x_407_ = l_term_x25_x5b___x7c___x5d___closed__2;
            leanh::lean_inc_n(v___x_405_, 5);
            v___x_408_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_408_, 0, v___x_405_);
            leanh::lean_ctor_set(v___x_408_, 1, v___x_407_);
            v___x_409_ = l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit___closed__15;
            v___x_410_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__0), core::ptr::addr_of_mut!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__0_once), _init_l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__0);
            v___x_411_ = l_Array_appendCore___redArg(v___x_410_, v_elems_398_);
            leanh::lean_dec_ref(v_elems_398_);
            v___x_412_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_412_, 0, v___x_405_);
            leanh::lean_ctor_set(v___x_412_, 1, v___x_409_);
            leanh::lean_ctor_set(v___x_412_, 2, v___x_411_);
            v___x_413_ = l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__1;
            v___x_414_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_414_, 0, v___x_405_);
            leanh::lean_ctor_set(v___x_414_, 1, v___x_413_);
            v___x_415_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3), core::ptr::addr_of_mut!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3_once), _init_l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3);
            v___x_416_ = l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5;
            leanh::lean_inc(v_currMacroScope_403_);
            leanh::lean_inc(v_quotContext_402_);
            v___x_417_ =
                l_Lean_addMacroScope(v_quotContext_402_, v___x_416_, v_currMacroScope_403_);
            v___x_418_ = l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__9;
            v___x_419_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
            leanh::lean_ctor_set(v___x_419_, 0, v___x_405_);
            leanh::lean_ctor_set(v___x_419_, 1, v___x_415_);
            leanh::lean_ctor_set(v___x_419_, 2, v___x_417_);
            leanh::lean_ctor_set(v___x_419_, 3, v___x_418_);
            v___x_420_ = l_term_x5b___x5d___closed__17;
            v___x_421_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_421_, 0, v___x_405_);
            leanh::lean_ctor_set(v___x_421_, 1, v___x_420_);
            v___x_422_ = l_Lean_Syntax_node5(
                v___x_405_, v___x_406_, v___x_408_, v___x_412_, v___x_414_, v___x_419_, v___x_421_,
            );
            v___x_423_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_423_, 0, v___x_422_);
            leanh::lean_ctor_set(v___x_423_, 1, v_a_391_);
            return v___x_423_;
        } else {
            let mut v_quotContext_424_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_425_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_ref_426_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_429_: u8 = 0;
            let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_437_: u8 = 0;
            let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_quotContext_424_ = leanh::lean_ctor_get(v_a_390_, 1);
            v_currMacroScope_425_ = leanh::lean_ctor_get(v_a_390_, 2);
            v_ref_426_ = leanh::lean_ctor_get(v_a_390_, 5);
            v___x_427_ = leanh::lean_unsigned_to_nat(0);
            v___x_428_ = leanh::lean_unsigned_to_nat(2);
            v___x_429_ = 0;
            v___x_430_ = l_Lean_SourceInfo_fromRef(v_ref_426_, v___x_429_);
            v___x_431_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3), core::ptr::addr_of_mut!(l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3_once), _init_l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__3);
            v___x_432_ = l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__5;
            leanh::lean_inc(v_currMacroScope_425_);
            leanh::lean_inc(v_quotContext_424_);
            v___x_433_ =
                l_Lean_addMacroScope(v_quotContext_424_, v___x_432_, v_currMacroScope_425_);
            v___x_434_ = l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___closed__9;
            v___x_435_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
            leanh::lean_ctor_set(v___x_435_, 0, v___x_430_);
            leanh::lean_ctor_set(v___x_435_, 1, v___x_431_);
            leanh::lean_ctor_set(v___x_435_, 2, v___x_433_);
            leanh::lean_ctor_set(v___x_435_, 3, v___x_434_);
            v___x_436_ = lean_nat_mod(v_size_399_, v___x_428_);
            v___x_437_ = lean_nat_dec_eq(v___x_436_, v___x_427_);
            leanh::lean_dec(v___x_436_);
            v___x_438_ = l___private_Init_Data_List_Notation_0__Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1_expandListLit(v_elems_398_, v_size_399_, v___x_437_, v___x_435_, v_a_390_, v_a_391_);
            leanh::lean_dec_ref(v_elems_398_);
            return v___x_438_;
        }
    }
}
pub unsafe fn l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1___boxed(
    mut v_x_439_: *mut leanh::LeanObject,
    mut v_a_440_: *mut leanh::LeanObject,
    mut v_a_441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_442_ = l_Lean___aux__Init__Data__List__Notation______macroRules__term_x5b___x5d__1(
        v_x_439_, v_a_440_, v_a_441_,
    );
    leanh::lean_dec_ref(v_a_440_);
    return v_res_442_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Notation(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Notation(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Notation(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_Notation(builtin);
}