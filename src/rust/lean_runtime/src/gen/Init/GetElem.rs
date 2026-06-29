// Lean compiler output
// Module: Init.GetElem
// Imports: Init.Util Init.Data.Option.Basic
use crate::r#gen::Init::Data::Option::Basic::{
    initialize_Init_Data_Option_Basic, runtime_initialize_Init_Data_Option_Basic,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node5, l_Lean_addMacroScope,
    l_Lean_mkAtom, l_List_get___redArg, l_String_toRawSubstring_x27, l_panic___redArg,
};
use crate::r#gen::Init::Util::{
    initialize_Init_Util, l_mkPanicMessageWithDecl, runtime_initialize_Init_Util,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_string_utf8_byte_size,
};
pub static l_outOfBounds___redArg___closed__0_value: crate::leanh::LeanStringObject<13> =
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
        m_data: [73, 110, 105, 116, 46, 71, 101, 116, 69, 108, 101, 109, 0],
    };
static mut l_outOfBounds___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_outOfBounds___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_outOfBounds___redArg___closed__1_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [111, 117, 116, 79, 102, 66, 111, 117, 110, 100, 115, 0],
    };
static mut l_outOfBounds___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_outOfBounds___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_outOfBounds___redArg___closed__2_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            105, 110, 100, 101, 120, 32, 111, 117, 116, 32, 111, 102, 32, 98, 111, 117, 110, 100,
            115, 0,
        ],
    };
static mut l_outOfBounds___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_outOfBounds___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [116, 101, 114, 109, 95, 95, 91, 95, 93, 0],
    };
static mut l_term_____x5b___x5d___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17746073143502587047 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__2_value: crate::leanh::LeanStringObject<8> =
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
static mut l_term_____x5b___x5d___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__2_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__4_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [110, 111, 87, 115, 0],
    };
static mut l_term_____x5b___x5d___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__4_value)
                as *mut crate::leanh::LeanObject,
            1581446985683836252 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__6_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(l_term_____x5b___x5d___closed__5_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_term_____x5b___x5d___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__7_value: crate::leanh::LeanStringObject<2> =
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
static mut l_term_____x5b___x5d___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__8_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_term_____x5b___x5d___closed__7_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_term_____x5b___x5d___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__10_value: crate::leanh::LeanStringObject<16> =
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
static mut l_term_____x5b___x5d___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__10_value)
                as *mut crate::leanh::LeanObject,
            1164644006045091397 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__12_value: crate::leanh::LeanStringObject<5> =
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
static mut l_term_____x5b___x5d___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__13_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__12_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__14_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__13_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__15_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__11_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__16_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__17_value: crate::leanh::LeanStringObject<2> =
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
static mut l_term_____x5b___x5d___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__18_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_term_____x5b___x5d___closed__17_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_term_____x5b___x5d___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__19_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__16_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__20_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__19_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__20_value) as *mut crate::leanh::LeanObject;
pub static mut l_term_____x5b___x5d: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
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
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__2_value:
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
    m_data: [84, 101, 114, 109, 0],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__3_value:
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
    m_data: [97, 112, 112, 0],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__3_value
) as *mut crate::leanh::LeanObject;
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_0:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_1:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_2:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        12966880221525079621 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [103, 101, 116, 69, 108, 101, 109, 0],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__7_value:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5_value
        ) as *mut crate::leanh::LeanObject,
        18081053125345290886 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__8_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [71, 101, 116, 69, 108, 101, 109, 0],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__8_value
) as *mut crate::leanh::LeanObject;
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__9_value_aux_0:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__8_value
        ) as *mut crate::leanh::LeanObject,
        854136310249810287 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__9_value:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__9_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5_value
        ) as *mut crate::leanh::LeanObject,
        8801718159307809986 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__10_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__9_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__11_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__10_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__11_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__12_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__12_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13_value:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__12_value
        ) as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__14_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__14_value
) as *mut crate::leanh::LeanObject;
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value_aux_0:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value_aux_1:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value_aux_2:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__14_value
        ) as *mut crate::leanh::LeanObject,
        7932075773091973500 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__16_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
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
        104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__16_value
) as *mut crate::leanh::LeanObject;
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value_aux_0:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value_aux_1:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value_aux_2:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__16_value
        ) as *mut crate::leanh::LeanObject,
        7306243862518720553 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__18_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
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
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__18_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__19_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__19_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__20_value:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__19_value
        ) as *mut crate::leanh::LeanObject,
        9871775667037945883 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__20_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__21_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__21_value
) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__23_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__23_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__24_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__23_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__24_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__25_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [98, 121, 84, 97, 99, 116, 105, 99, 0],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__25_value
) as *mut crate::leanh::LeanObject;
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value_aux_0:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value_aux_1:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value_aux_2:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__25_value
        ) as *mut crate::leanh::LeanObject,
        16173796135615239867 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__27_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [98, 121, 0],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__27_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
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
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__29_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__29:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__29_value
) as *mut crate::leanh::LeanObject;
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value_aux_0:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value_aux_1:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value_aux_2:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__29_value
        ) as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__31_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
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
        116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__31:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__31_value
) as *mut crate::leanh::LeanObject;
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value_aux_0:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value_aux_1:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value_aux_2:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__31_value
        ) as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__33_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
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
        116, 97, 99, 116, 105, 99, 71, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116, 105,
        99, 0,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__33:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__33_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__34_value:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__33_value
        ) as *mut crate::leanh::LeanObject,
        3731765604234633101 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__34:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__34_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__35_value:
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
        103, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116, 105, 99, 0,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__35:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__35_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__36_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
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
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__36:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__36_value
) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d_x27___00__closed__0_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [116, 101, 114, 109, 95, 95, 91, 95, 93, 39, 95, 0],
    };
static mut l_term_____x5b___x5d_x27___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d_x27___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            14552850886997009045 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d_x27___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d_x27___00__closed__2_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [93, 39, 0],
    };
static mut l_term_____x5b___x5d_x27___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d_x27___00__closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d_x27___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d_x27___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__16_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d_x27___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d_x27___00__closed__5_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__13_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d_x27___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d_x27___00__closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d_x27___00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d_x27___00__closed__7_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d_x27___00__closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_term_____x5b___x5d_x27__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__0_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [116, 101, 114, 109, 95, 95, 91, 95, 93, 95, 63, 0],
    };
static mut l_term_____x5b___x5d___x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            1231705503909655209 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__2_value: crate::leanh::LeanStringObject<6> =
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
static mut l_term_____x5b___x5d___x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2214559063752339918 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__4_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x3f___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x3f___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__9_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [63, 0],
    };
static mut l_term_____x5b___x5d___x3f___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__10_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x3f___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x3f___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__12_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x3f___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_term_____x5b___x5d___x3f: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [103, 101, 116, 69, 108, 101, 109, 63, 0],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__2_value:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        12289893685329059214 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__3_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [71, 101, 116, 69, 108, 101, 109, 63, 0],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__3_value
) as *mut crate::leanh::LeanObject;
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__3_value) as *mut crate::leanh::LeanObject,1284173141442213452 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0_value) as *mut crate::leanh::LeanObject,14790288273250445109 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__5_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__6_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__5_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___x21___closed__0_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [116, 101, 114, 109, 95, 95, 91, 95, 93, 95, 33, 0],
    };
static mut l_term_____x5b___x5d___x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___x21___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__0_value)
                as *mut crate::leanh::LeanObject,
            941824322364543252 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___x21___closed__2_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [33, 0],
    };
static mut l_term_____x5b___x5d___x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___x21___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x21___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___x21___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x21___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_term_____x5b___x5d___x21___closed__5_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x21___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_term_____x5b___x5d___x21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [103, 101, 116, 69, 108, 101, 109, 33, 0],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__2_value:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        14784475134464642716 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__2_value
) as *mut crate::leanh::LeanObject;
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__3_value) as *mut crate::leanh::LeanObject,1284173141442213452 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0_value) as *mut crate::leanh::LeanObject,16409410464876292983 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__4_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__5_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [105, 110, 116, 114, 111, 115, 0],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_0:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_1:
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_2:
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value:
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__1_value)
            as *mut crate::leanh::LeanObject,
        3278676588586250010 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 1,
    },
    m_objs: [
        (((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__10_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [116, 97, 99, 116, 105, 99, 84, 114, 121, 95, 0],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value_aux_0:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value_aux_1:
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value_aux_2:
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value:
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__10_value)
            as *mut crate::leanh::LeanObject,
        10962186005905108258 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__12_value:
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
    m_data: [116, 114, 121, 0],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__15_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [116, 97, 99, 116, 105, 99, 95, 60, 59, 62, 95, 0],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__15_value)
        as *mut crate::leanh::LeanObject;
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value_aux_0:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value_aux_1:
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value_aux_2:
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value:
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__15_value)
            as *mut crate::leanh::LeanObject,
        12695378809397736991 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__17_value:
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
    m_data: [115, 105, 109, 112, 0],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__17_value)
        as *mut crate::leanh::LeanObject;
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value_aux_0:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value_aux_1:
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value_aux_2:
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value:
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__17_value)
            as *mut crate::leanh::LeanObject,
        12783917532758215986 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value)
        as *mut crate::leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__21_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__21_value)
        as *mut crate::leanh::LeanObject;
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value_aux_0:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value_aux_1:
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value_aux_2:
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value:
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__21_value)
            as *mut crate::leanh::LeanObject,
        3488656302031949961 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value)
        as *mut crate::leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__27_value:
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
    m_data: [111, 110, 108, 121, 0],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__27:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__27_value)
        as *mut crate::leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__34_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [115, 105, 109, 112, 76, 101, 109, 109, 97, 0],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__34:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__34_value)
        as *mut crate::leanh::LeanObject;
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value_aux_0:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value_aux_1:
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value_aux_2:
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value:
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__34_value)
            as *mut crate::leanh::LeanObject,
        7383208167966365478 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value)
        as *mut crate::leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__52_value:
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
    m_data: [60, 59, 62, 0],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__52:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__52_value)
        as *mut crate::leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [99, 111, 110, 103, 114, 0],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55_value)
        as *mut crate::leanh::LeanObject;
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value_aux_0:
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
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value_aux_1:
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value_aux_2:
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value:
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55_value)
            as *mut crate::leanh::LeanObject,
        7757010358911522857 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value)
        as *mut crate::leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_LawfulGetElem_getElem_x3f__def___autoParam: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_LawfulGetElem_getElem_x21__def___autoParam___closed__6_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
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
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_LawfulGetElem_getElem_x21__def___autoParam___closed__11_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        111, 117, 116, 79, 102, 66, 111, 117, 110, 100, 115, 95, 101, 113, 95, 100, 101, 102, 97,
        117, 108, 116, 0,
    ],
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_LawfulGetElem_getElem_x21__def___autoParam___closed__14_value:
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__11_value)
            as *mut crate::leanh::LeanObject,
        4748755860924891891 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__25_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__26_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__27_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__28_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__29_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__29:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__30_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__30:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__31_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__31:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_LawfulGetElem_getElem_x21__def___autoParam: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [116, 97, 99, 116, 105, 99, 71, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116, 105, 99, 95, 101, 120, 116, 101, 110, 115, 105, 98, 108, 101, 0]};
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value) as *mut crate::leanh::LeanObject,7705027380931481693 as *mut crate::leanh::LeanObject] };
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 101, 113, 49, 0]};
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut crate::leanh::LeanObject,8471002125274025202 as *mut crate::leanh::LeanObject] };
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__14_value) as *mut crate::leanh::LeanObject,8689124066155232629 as *mut crate::leanh::LeanObject] };
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [119, 105, 116, 104, 82, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value) as *mut crate::leanh::LeanObject;
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value) as *mut crate::leanh::LeanObject,6022092293134036165 as *mut crate::leanh::LeanObject] };
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [119, 105, 116, 104, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 112, 112, 108, 121, 0]};
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value) as *mut crate::leanh::LeanObject;
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value) as *mut crate::leanh::LeanObject,5826123769708379594 as *mut crate::leanh::LeanObject] };
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [70, 105, 110, 46, 118, 97, 108, 95, 108, 116, 95, 111, 102, 95, 108, 101, 0]};
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [70, 105, 110, 0]};
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [118, 97, 108, 95, 108, 116, 95, 111, 102, 95, 108, 101, 0]};
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value) as *mut crate::leanh::LeanObject;
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value) as *mut crate::leanh::LeanObject,15815496672699636542 as *mut crate::leanh::LeanObject] };
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value) as *mut crate::leanh::LeanObject,11955149997473870394 as *mut crate::leanh::LeanObject] };
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [103, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116, 105, 99, 95, 101, 120, 116, 101, 110, 115, 105, 98, 108, 101, 0]};
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 111, 110, 101, 0]};
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value) as *mut crate::leanh::LeanObject;
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value) as *mut crate::leanh::LeanObject,8876691400619696497 as *mut crate::leanh::LeanObject] };
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_List_instGetElemNatLtLength___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_List_instGetElemNatLtLength___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_List_instGetElemNatLtLength___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_instGetElemNatLtLength___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_get_x21Internal___redArg___closed__0_value: crate::leanh::LeanStringObject<18> =
    crate::leanh::LeanStringObject {
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
            76, 105, 115, 116, 46, 103, 101, 116, 33, 73, 110, 116, 101, 114, 110, 97, 108, 0,
        ],
    };
static mut l_List_get_x21Internal___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_get_x21Internal___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_get_x21Internal___redArg___closed__1_value: crate::leanh::LeanStringObject<14> =
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
            105, 110, 118, 97, 108, 105, 100, 32, 105, 110, 100, 101, 120, 0,
        ],
    };
static mut l_List_get_x21Internal___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_get_x21Internal___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_instGetElem_x3fNatLtLength___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_List_get_x3fInternal___redArg___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_List_instGetElem_x3fNatLtLength___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_instGetElem_x3fNatLtLength___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_instGetElem_x3fNatLtLength___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_List_get_x21Internal___redArg___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_List_instGetElem_x3fNatLtLength___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_instGetElem_x3fNatLtLength___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_instGetElem_x3fNatLtLength___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_List_instGetElemNatLtLength___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_instGetElem_x3fNatLtLength___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_instGetElem_x3fNatLtLength___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_instGetElem_x3fNatLtLength___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_instGetElem_x3fNatLtLength___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_instGetElemNatLtSize___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Array_instGetElemNatLtSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_instGetElemNatLtSize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_instGetElemNatLtSize___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_instGetElem_x3fNatLtSize___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Array_instGetElem_x3fNatLtSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_instGetElem_x3fNatLtSize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_instGetElem_x3fNatLtSize___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_instGetElem_x3fNatLtSize___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Array_instGetElem_x3fNatLtSize___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_instGetElem_x3fNatLtSize___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_instGetElem_x3fNatLtSize___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_instGetElem_x3fNatLtSize___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_instGetElemNatLtSize___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_instGetElem_x3fNatLtSize___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_instGetElem_x3fNatLtSize___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_instGetElem_x3fNatLtSize___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_instGetElem_x3fNatLtSize___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instGetElemNatTrue___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Syntax_instGetElemNatTrue___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Syntax_instGetElemNatTrue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instGetElemNatTrue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Syntax_instGetElemNatTrue: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instGetElemNatTrue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_outOfBounds___redArg(
    mut v_inst_1105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1106_ = l_outOfBounds___redArg___closed__0;
    v___x_1107_ = l_outOfBounds___redArg___closed__1;
    v___x_1108_ = crate::leanh::lean_unsigned_to_nat(18);
    v___x_1109_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1110_ = l_outOfBounds___redArg___closed__2;
    v___x_1111_ = l_mkPanicMessageWithDecl(
        v___x_1106_,
        v___x_1107_,
        v___x_1108_,
        v___x_1109_,
        v___x_1110_,
    );
    v___x_1112_ = l_panic___redArg(v_inst_1105_, v___x_1111_);
    return v___x_1112_;
}
pub unsafe fn l_outOfBounds___redArg___boxed(
    mut v_inst_1113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1114_ = l_outOfBounds___redArg(v_inst_1113_);
    crate::leanh::lean_dec(v_inst_1113_);
    return v_res_1114_;
}
pub unsafe fn l_outOfBounds(
    mut v_00_u03b1_1115_: *mut crate::leanh::LeanObject,
    mut v_inst_1116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1117_ = l_outOfBounds___redArg(v_inst_1116_);
    return v___x_1117_;
}
pub unsafe fn l_outOfBounds___boxed(
    mut v_00_u03b1_1118_: *mut crate::leanh::LeanObject,
    mut v_inst_1119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1120_ = l_outOfBounds(v_00_u03b1_1118_, v_inst_1119_);
    crate::leanh::lean_dec(v_inst_1119_);
    return v_res_1120_;
}
pub unsafe fn _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1178_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5;
    v___x_1179_ = l_String_toRawSubstring_x27(v___x_1178_);
    return v___x_1179_;
}
pub unsafe fn _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1212_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__21;
    v___x_1213_ = l_String_toRawSubstring_x27(v___x_1212_);
    return v___x_1213_;
}
pub unsafe fn l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1(
    mut v_x_1244_: *mut crate::leanh::LeanObject,
    mut v_a_1245_: *mut crate::leanh::LeanObject,
    mut v_a_1246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: u8 = 0;
    v___x_1247_ = l_term_____x5b___x5d___closed__1;
    crate::leanh::lean_inc(v_x_1244_);
    v___x_1248_ = l_Lean_Syntax_isOfKind(v_x_1244_, v___x_1247_);
    if v___x_1248_ == 0 {
        let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1244_);
        v___x_1249_ = crate::leanh::lean_box(1);
        v___x_1250_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1250_, 0, v___x_1249_);
        crate::leanh::lean_ctor_set(v___x_1250_, 1, v_a_1246_);
        return v___x_1250_;
    } else {
        let mut v_quotContext_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1258_: u8 = 0;
        let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1251_ = crate::leanh::lean_ctor_get(v_a_1245_, 1);
        v_currMacroScope_1252_ = crate::leanh::lean_ctor_get(v_a_1245_, 2);
        v_ref_1253_ = crate::leanh::lean_ctor_get(v_a_1245_, 5);
        v___x_1254_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1255_ = l_Lean_Syntax_getArg(v_x_1244_, v___x_1254_);
        v___x_1256_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_1257_ = l_Lean_Syntax_getArg(v_x_1244_, v___x_1256_);
        crate::leanh::lean_dec(v_x_1244_);
        v___x_1258_ = 0;
        v___x_1259_ = l_Lean_SourceInfo_fromRef(v_ref_1253_, v___x_1258_);
        v___x_1260_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4;
        v___x_1261_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6_once
            ),
            _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6,
        );
        v___x_1262_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__7;
        crate::leanh::lean_inc_n(v_currMacroScope_1252_, 2);
        crate::leanh::lean_inc_n(v_quotContext_1251_, 2);
        v___x_1263_ =
            l_Lean_addMacroScope(v_quotContext_1251_, v___x_1262_, v_currMacroScope_1252_);
        v___x_1264_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__11;
        crate::leanh::lean_inc_n(v___x_1259_, 15);
        v___x_1265_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1265_, 0, v___x_1259_);
        crate::leanh::lean_ctor_set(v___x_1265_, 1, v___x_1261_);
        crate::leanh::lean_ctor_set(v___x_1265_, 2, v___x_1263_);
        crate::leanh::lean_ctor_set(v___x_1265_, 3, v___x_1264_);
        v___x_1266_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
        v___x_1267_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15;
        v___x_1268_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17;
        v___x_1269_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__18;
        v___x_1270_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1270_, 0, v___x_1259_);
        crate::leanh::lean_ctor_set(v___x_1270_, 1, v___x_1269_);
        v___x_1271_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__20;
        v___x_1272_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22_once
            ),
            _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22,
        );
        v___x_1273_ = crate::leanh::lean_box(0);
        v___x_1274_ =
            l_Lean_addMacroScope(v_quotContext_1251_, v___x_1273_, v_currMacroScope_1252_);
        v___x_1275_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__24;
        v___x_1276_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1276_, 0, v___x_1259_);
        crate::leanh::lean_ctor_set(v___x_1276_, 1, v___x_1272_);
        crate::leanh::lean_ctor_set(v___x_1276_, 2, v___x_1274_);
        crate::leanh::lean_ctor_set(v___x_1276_, 3, v___x_1275_);
        v___x_1277_ = l_Lean_Syntax_node1(v___x_1259_, v___x_1271_, v___x_1276_);
        v___x_1278_ = l_Lean_Syntax_node2(v___x_1259_, v___x_1268_, v___x_1270_, v___x_1277_);
        v___x_1279_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26;
        v___x_1280_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__27;
        v___x_1281_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1281_, 0, v___x_1259_);
        crate::leanh::lean_ctor_set(v___x_1281_, 1, v___x_1280_);
        v___x_1282_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30;
        v___x_1283_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32;
        v___x_1284_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__34;
        v___x_1285_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__35;
        v___x_1286_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1286_, 0, v___x_1259_);
        crate::leanh::lean_ctor_set(v___x_1286_, 1, v___x_1285_);
        v___x_1287_ = l_Lean_Syntax_node1(v___x_1259_, v___x_1284_, v___x_1286_);
        v___x_1288_ = l_Lean_Syntax_node1(v___x_1259_, v___x_1266_, v___x_1287_);
        v___x_1289_ = l_Lean_Syntax_node1(v___x_1259_, v___x_1283_, v___x_1288_);
        v___x_1290_ = l_Lean_Syntax_node1(v___x_1259_, v___x_1282_, v___x_1289_);
        v___x_1291_ = l_Lean_Syntax_node2(v___x_1259_, v___x_1279_, v___x_1281_, v___x_1290_);
        v___x_1292_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__36;
        v___x_1293_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1293_, 0, v___x_1259_);
        crate::leanh::lean_ctor_set(v___x_1293_, 1, v___x_1292_);
        v___x_1294_ = l_Lean_Syntax_node3(
            v___x_1259_,
            v___x_1267_,
            v___x_1278_,
            v___x_1291_,
            v___x_1293_,
        );
        v___x_1295_ = l_Lean_Syntax_node3(
            v___x_1259_,
            v___x_1266_,
            v___x_1255_,
            v___x_1257_,
            v___x_1294_,
        );
        v___x_1296_ = l_Lean_Syntax_node2(v___x_1259_, v___x_1260_, v___x_1265_, v___x_1295_);
        v___x_1297_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1297_, 0, v___x_1296_);
        crate::leanh::lean_ctor_set(v___x_1297_, 1, v_a_1246_);
        return v___x_1297_;
    }
}
pub unsafe fn l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___boxed(
    mut v_x_1298_: *mut crate::leanh::LeanObject,
    mut v_a_1299_: *mut crate::leanh::LeanObject,
    mut v_a_1300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1301_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1(
        v_x_1298_, v_a_1299_, v_a_1300_,
    );
    crate::leanh::lean_dec_ref(v_a_1299_);
    return v_res_1301_;
}
pub unsafe fn l___aux__Init__GetElem______macroRules__term_____x5b___x5d_x27____1(
    mut v_x_1325_: *mut crate::leanh::LeanObject,
    mut v_a_1326_: *mut crate::leanh::LeanObject,
    mut v_a_1327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: u8 = 0;
    v___x_1328_ = l_term_____x5b___x5d_x27___00__closed__1;
    crate::leanh::lean_inc(v_x_1325_);
    v___x_1329_ = l_Lean_Syntax_isOfKind(v_x_1325_, v___x_1328_);
    if v___x_1329_ == 0 {
        let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1325_);
        v___x_1330_ = crate::leanh::lean_box(1);
        v___x_1331_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1331_, 0, v___x_1330_);
        crate::leanh::lean_ctor_set(v___x_1331_, 1, v_a_1327_);
        return v___x_1331_;
    } else {
        let mut v_quotContext_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1341_: u8 = 0;
        let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1332_ = crate::leanh::lean_ctor_get(v_a_1326_, 1);
        v_currMacroScope_1333_ = crate::leanh::lean_ctor_get(v_a_1326_, 2);
        v_ref_1334_ = crate::leanh::lean_ctor_get(v_a_1326_, 5);
        v___x_1335_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1336_ = l_Lean_Syntax_getArg(v_x_1325_, v___x_1335_);
        v___x_1337_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_1338_ = l_Lean_Syntax_getArg(v_x_1325_, v___x_1337_);
        v___x_1339_ = crate::leanh::lean_unsigned_to_nat(4);
        v___x_1340_ = l_Lean_Syntax_getArg(v_x_1325_, v___x_1339_);
        crate::leanh::lean_dec(v_x_1325_);
        v___x_1341_ = 0;
        v___x_1342_ = l_Lean_SourceInfo_fromRef(v_ref_1334_, v___x_1341_);
        v___x_1343_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4;
        v___x_1344_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6_once
            ),
            _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6,
        );
        v___x_1345_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__7;
        crate::leanh::lean_inc(v_currMacroScope_1333_);
        crate::leanh::lean_inc(v_quotContext_1332_);
        v___x_1346_ =
            l_Lean_addMacroScope(v_quotContext_1332_, v___x_1345_, v_currMacroScope_1333_);
        v___x_1347_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__11;
        crate::leanh::lean_inc_n(v___x_1342_, 2);
        v___x_1348_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1348_, 0, v___x_1342_);
        crate::leanh::lean_ctor_set(v___x_1348_, 1, v___x_1344_);
        crate::leanh::lean_ctor_set(v___x_1348_, 2, v___x_1346_);
        crate::leanh::lean_ctor_set(v___x_1348_, 3, v___x_1347_);
        v___x_1349_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
        v___x_1350_ = l_Lean_Syntax_node3(
            v___x_1342_,
            v___x_1349_,
            v___x_1336_,
            v___x_1338_,
            v___x_1340_,
        );
        v___x_1351_ = l_Lean_Syntax_node2(v___x_1342_, v___x_1343_, v___x_1348_, v___x_1350_);
        v___x_1352_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1352_, 0, v___x_1351_);
        crate::leanh::lean_ctor_set(v___x_1352_, 1, v_a_1327_);
        return v___x_1352_;
    }
}
pub unsafe fn l___aux__Init__GetElem______macroRules__term_____x5b___x5d_x27____1___boxed(
    mut v_x_1353_: *mut crate::leanh::LeanObject,
    mut v_a_1354_: *mut crate::leanh::LeanObject,
    mut v_a_1355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1356_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d_x27____1(
        v_x_1353_, v_a_1354_, v_a_1355_,
    );
    crate::leanh::lean_dec_ref(v_a_1354_);
    return v_res_1356_;
}
pub unsafe fn l_decidableGetElem_x3f___redArg(
    mut v_inst_1357_: *mut crate::leanh::LeanObject,
    mut v_xs_1358_: *mut crate::leanh::LeanObject,
    mut v_i_1359_: *mut crate::leanh::LeanObject,
    mut v_inst_1360_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_inst_1360_ == 0 {
        let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_i_1359_);
        crate::leanh::lean_dec(v_xs_1358_);
        crate::leanh::lean_dec(v_inst_1357_);
        v___x_1361_ = crate::leanh::lean_box(0);
        return v___x_1361_;
    } else {
        let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1362_ = crate::leanh::lean_apply_3(
            v_inst_1357_,
            v_xs_1358_,
            v_i_1359_,
            crate::leanh::lean_box(0),
        );
        v___x_1363_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1363_, 0, v___x_1362_);
        return v___x_1363_;
    }
}
pub unsafe fn l_decidableGetElem_x3f___redArg___boxed(
    mut v_inst_1364_: *mut crate::leanh::LeanObject,
    mut v_xs_1365_: *mut crate::leanh::LeanObject,
    mut v_i_1366_: *mut crate::leanh::LeanObject,
    mut v_inst_1367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_16__boxed_1368_: u8 = 0;
    let mut v_res_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inst_16__boxed_1368_ = (crate::leanh::lean_unbox(v_inst_1367_) as u8);
    v_res_1369_ = l_decidableGetElem_x3f___redArg(
        v_inst_1364_,
        v_xs_1365_,
        v_i_1366_,
        v_inst_16__boxed_1368_,
    );
    return v_res_1369_;
}
pub unsafe fn l_decidableGetElem_x3f(
    mut v_coll_1370_: *mut crate::leanh::LeanObject,
    mut v_idx_1371_: *mut crate::leanh::LeanObject,
    mut v_elem_1372_: *mut crate::leanh::LeanObject,
    mut v_valid_1373_: *mut crate::leanh::LeanObject,
    mut v_inst_1374_: *mut crate::leanh::LeanObject,
    mut v_xs_1375_: *mut crate::leanh::LeanObject,
    mut v_i_1376_: *mut crate::leanh::LeanObject,
    mut v_inst_1377_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_inst_1377_ == 0 {
        let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_i_1376_);
        crate::leanh::lean_dec(v_xs_1375_);
        crate::leanh::lean_dec(v_inst_1374_);
        v___x_1378_ = crate::leanh::lean_box(0);
        return v___x_1378_;
    } else {
        let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1379_ = crate::leanh::lean_apply_3(
            v_inst_1374_,
            v_xs_1375_,
            v_i_1376_,
            crate::leanh::lean_box(0),
        );
        v___x_1380_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1380_, 0, v___x_1379_);
        return v___x_1380_;
    }
}
pub unsafe fn l_decidableGetElem_x3f___boxed(
    mut v_coll_1381_: *mut crate::leanh::LeanObject,
    mut v_idx_1382_: *mut crate::leanh::LeanObject,
    mut v_elem_1383_: *mut crate::leanh::LeanObject,
    mut v_valid_1384_: *mut crate::leanh::LeanObject,
    mut v_inst_1385_: *mut crate::leanh::LeanObject,
    mut v_xs_1386_: *mut crate::leanh::LeanObject,
    mut v_i_1387_: *mut crate::leanh::LeanObject,
    mut v_inst_1388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_28__boxed_1389_: u8 = 0;
    let mut v_res_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inst_28__boxed_1389_ = (crate::leanh::lean_unbox(v_inst_1388_) as u8);
    v_res_1390_ = l_decidableGetElem_x3f(
        v_coll_1381_,
        v_idx_1382_,
        v_elem_1383_,
        v_valid_1384_,
        v_inst_1385_,
        v_xs_1386_,
        v_i_1387_,
        v_inst_28__boxed_1389_,
    );
    return v_res_1390_;
}
pub unsafe fn _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1430_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0;
    v___x_1431_ = l_String_toRawSubstring_x27(v___x_1430_);
    return v___x_1431_;
}
pub unsafe fn l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1(
    mut v_x_1444_: *mut crate::leanh::LeanObject,
    mut v_a_1445_: *mut crate::leanh::LeanObject,
    mut v_a_1446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: u8 = 0;
    v___x_1447_ = l_term_____x5b___x5d___x3f___closed__1;
    crate::leanh::lean_inc(v_x_1444_);
    v___x_1448_ = l_Lean_Syntax_isOfKind(v_x_1444_, v___x_1447_);
    if v___x_1448_ == 0 {
        let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1444_);
        v___x_1449_ = crate::leanh::lean_box(1);
        v___x_1450_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1450_, 0, v___x_1449_);
        crate::leanh::lean_ctor_set(v___x_1450_, 1, v_a_1446_);
        return v___x_1450_;
    } else {
        let mut v_quotContext_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1458_: u8 = 0;
        let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1451_ = crate::leanh::lean_ctor_get(v_a_1445_, 1);
        v_currMacroScope_1452_ = crate::leanh::lean_ctor_get(v_a_1445_, 2);
        v_ref_1453_ = crate::leanh::lean_ctor_get(v_a_1445_, 5);
        v___x_1454_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1455_ = l_Lean_Syntax_getArg(v_x_1444_, v___x_1454_);
        v___x_1456_ = crate::leanh::lean_unsigned_to_nat(3);
        v___x_1457_ = l_Lean_Syntax_getArg(v_x_1444_, v___x_1456_);
        crate::leanh::lean_dec(v_x_1444_);
        v___x_1458_ = 0;
        v___x_1459_ = l_Lean_SourceInfo_fromRef(v_ref_1453_, v___x_1458_);
        v___x_1460_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4;
        v___x_1461_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1), core::ptr::addr_of_mut!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1_once), _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1);
        v___x_1462_ =
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__2;
        crate::leanh::lean_inc(v_currMacroScope_1452_);
        crate::leanh::lean_inc(v_quotContext_1451_);
        v___x_1463_ =
            l_Lean_addMacroScope(v_quotContext_1451_, v___x_1462_, v_currMacroScope_1452_);
        v___x_1464_ =
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__6;
        crate::leanh::lean_inc_n(v___x_1459_, 2);
        v___x_1465_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1465_, 0, v___x_1459_);
        crate::leanh::lean_ctor_set(v___x_1465_, 1, v___x_1461_);
        crate::leanh::lean_ctor_set(v___x_1465_, 2, v___x_1463_);
        crate::leanh::lean_ctor_set(v___x_1465_, 3, v___x_1464_);
        v___x_1466_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
        v___x_1467_ = l_Lean_Syntax_node2(v___x_1459_, v___x_1466_, v___x_1455_, v___x_1457_);
        v___x_1468_ = l_Lean_Syntax_node2(v___x_1459_, v___x_1460_, v___x_1465_, v___x_1467_);
        v___x_1469_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1469_, 0, v___x_1468_);
        crate::leanh::lean_ctor_set(v___x_1469_, 1, v_a_1446_);
        return v___x_1469_;
    }
}
pub unsafe fn l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___boxed(
    mut v_x_1470_: *mut crate::leanh::LeanObject,
    mut v_a_1471_: *mut crate::leanh::LeanObject,
    mut v_a_1472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1473_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1(
        v_x_1470_, v_a_1471_, v_a_1472_,
    );
    crate::leanh::lean_dec_ref(v_a_1471_);
    return v_res_1473_;
}
pub unsafe fn _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1491_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0;
    v___x_1492_ = l_String_toRawSubstring_x27(v___x_1491_);
    return v___x_1492_;
}
pub unsafe fn l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1(
    mut v_x_1504_: *mut crate::leanh::LeanObject,
    mut v_a_1505_: *mut crate::leanh::LeanObject,
    mut v_a_1506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: u8 = 0;
    v___x_1507_ = l_term_____x5b___x5d___x21___closed__1;
    crate::leanh::lean_inc(v_x_1504_);
    v___x_1508_ = l_Lean_Syntax_isOfKind(v_x_1504_, v___x_1507_);
    if v___x_1508_ == 0 {
        let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1504_);
        v___x_1509_ = crate::leanh::lean_box(1);
        v___x_1510_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1510_, 0, v___x_1509_);
        crate::leanh::lean_ctor_set(v___x_1510_, 1, v_a_1506_);
        return v___x_1510_;
    } else {
        let mut v_quotContext_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1518_: u8 = 0;
        let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1511_ = crate::leanh::lean_ctor_get(v_a_1505_, 1);
        v_currMacroScope_1512_ = crate::leanh::lean_ctor_get(v_a_1505_, 2);
        v_ref_1513_ = crate::leanh::lean_ctor_get(v_a_1505_, 5);
        v___x_1514_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1515_ = l_Lean_Syntax_getArg(v_x_1504_, v___x_1514_);
        v___x_1516_ = crate::leanh::lean_unsigned_to_nat(3);
        v___x_1517_ = l_Lean_Syntax_getArg(v_x_1504_, v___x_1516_);
        crate::leanh::lean_dec(v_x_1504_);
        v___x_1518_ = 0;
        v___x_1519_ = l_Lean_SourceInfo_fromRef(v_ref_1513_, v___x_1518_);
        v___x_1520_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4;
        v___x_1521_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1), core::ptr::addr_of_mut!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1_once), _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1);
        v___x_1522_ =
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__2;
        crate::leanh::lean_inc(v_currMacroScope_1512_);
        crate::leanh::lean_inc(v_quotContext_1511_);
        v___x_1523_ =
            l_Lean_addMacroScope(v_quotContext_1511_, v___x_1522_, v_currMacroScope_1512_);
        v___x_1524_ =
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__5;
        crate::leanh::lean_inc_n(v___x_1519_, 2);
        v___x_1525_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1525_, 0, v___x_1519_);
        crate::leanh::lean_ctor_set(v___x_1525_, 1, v___x_1521_);
        crate::leanh::lean_ctor_set(v___x_1525_, 2, v___x_1523_);
        crate::leanh::lean_ctor_set(v___x_1525_, 3, v___x_1524_);
        v___x_1526_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
        v___x_1527_ = l_Lean_Syntax_node2(v___x_1519_, v___x_1526_, v___x_1515_, v___x_1517_);
        v___x_1528_ = l_Lean_Syntax_node2(v___x_1519_, v___x_1520_, v___x_1525_, v___x_1527_);
        v___x_1529_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1529_, 0, v___x_1528_);
        crate::leanh::lean_ctor_set(v___x_1529_, 1, v_a_1506_);
        return v___x_1529_;
    }
}
pub unsafe fn l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___boxed(
    mut v_x_1530_: *mut crate::leanh::LeanObject,
    mut v_a_1531_: *mut crate::leanh::LeanObject,
    mut v_a_1532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1533_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1(
        v_x_1530_, v_a_1531_, v_a_1532_,
    );
    crate::leanh::lean_dec_ref(v_a_1531_);
    return v_res_1533_;
}
pub unsafe fn l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__0(
    mut v_inst_1534_: *mut crate::leanh::LeanObject,
    mut v_inst_1535_: *mut crate::leanh::LeanObject,
    mut v_xs_1536_: *mut crate::leanh::LeanObject,
    mut v_i_1537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: u8 = 0;
    crate::leanh::lean_inc(v_i_1537_);
    crate::leanh::lean_inc(v_xs_1536_);
    v___x_1538_ = crate::leanh::lean_apply_2(v_inst_1534_, v_xs_1536_, v_i_1537_);
    v___x_1539_ = (crate::leanh::lean_unbox(v___x_1538_) as u8);
    if v___x_1539_ == 0 {
        let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_i_1537_);
        crate::leanh::lean_dec(v_xs_1536_);
        crate::leanh::lean_dec(v_inst_1535_);
        v___x_1540_ = crate::leanh::lean_box(0);
        return v___x_1540_;
    } else {
        let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1541_ = crate::leanh::lean_apply_3(
            v_inst_1535_,
            v_xs_1536_,
            v_i_1537_,
            crate::leanh::lean_box(0),
        );
        v___x_1542_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1542_, 0, v___x_1541_);
        return v___x_1542_;
    }
}
pub unsafe fn l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1(
    mut v___f_1543_: *mut crate::leanh::LeanObject,
    mut v_inst_1544_: *mut crate::leanh::LeanObject,
    mut v_xs_1545_: *mut crate::leanh::LeanObject,
    mut v_i_1546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1547_ = crate::leanh::lean_apply_2(v___f_1543_, v_xs_1545_, v_i_1546_);
    if crate::leanh::lean_obj_tag(v___x_1547_) == 0 {
        let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1548_ = l_outOfBounds___redArg(v_inst_1544_);
        return v___x_1548_;
    } else {
        let mut v_val_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1549_ = crate::leanh::lean_ctor_get(v___x_1547_, 0);
        crate::leanh::lean_inc(v_val_1549_);
        crate::leanh::lean_dec_ref_known(v___x_1547_, 1);
        return v_val_1549_;
    }
}
pub unsafe fn l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1___boxed(
    mut v___f_1550_: *mut crate::leanh::LeanObject,
    mut v_inst_1551_: *mut crate::leanh::LeanObject,
    mut v_xs_1552_: *mut crate::leanh::LeanObject,
    mut v_i_1553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1554_ = l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1(
        v___f_1550_,
        v_inst_1551_,
        v_xs_1552_,
        v_i_1553_,
    );
    crate::leanh::lean_dec(v_inst_1551_);
    return v_res_1554_;
}
pub unsafe fn l_instGetElem_x3fOfGetElemOfDecidable___redArg(
    mut v_inst_1555_: *mut crate::leanh::LeanObject,
    mut v_inst_1556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_inst_1555_);
    v___f_1557_ = crate::leanh::lean_alloc_closure(
        l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1557_, 0, v_inst_1556_);
    crate::leanh::lean_closure_set(v___f_1557_, 1, v_inst_1555_);
    crate::leanh::lean_inc_ref(v___f_1557_);
    v___f_1558_ = crate::leanh::lean_alloc_closure(
        l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1558_, 0, v___f_1557_);
    v___x_1559_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1559_, 0, v_inst_1555_);
    crate::leanh::lean_ctor_set(v___x_1559_, 1, v___f_1557_);
    crate::leanh::lean_ctor_set(v___x_1559_, 2, v___f_1558_);
    return v___x_1559_;
}
pub unsafe fn l_instGetElem_x3fOfGetElemOfDecidable(
    mut v_coll_1560_: *mut crate::leanh::LeanObject,
    mut v_idx_1561_: *mut crate::leanh::LeanObject,
    mut v_elem_1562_: *mut crate::leanh::LeanObject,
    mut v_valid_1563_: *mut crate::leanh::LeanObject,
    mut v_inst_1564_: *mut crate::leanh::LeanObject,
    mut v_inst_1565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1566_ = l_instGetElem_x3fOfGetElemOfDecidable___redArg(v_inst_1564_, v_inst_1565_);
    return v___x_1566_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1575_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__1;
    v___x_1576_ = l_Lean_mkAtom(v___x_1575_);
    return v___x_1576_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1577_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3,
    );
    v___x_1578_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1579_ = lean_array_push(v___x_1578_, v___x_1577_);
    return v___x_1579_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1584_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5;
    v___x_1585_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4,
    );
    v___x_1586_ = lean_array_push(v___x_1585_, v___x_1584_);
    return v___x_1586_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1587_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6,
    );
    v___x_1588_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2;
    v___x_1589_ = crate::leanh::lean_box(2);
    v___x_1590_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1590_, 0, v___x_1589_);
    crate::leanh::lean_ctor_set(v___x_1590_, 1, v___x_1588_);
    crate::leanh::lean_ctor_set(v___x_1590_, 2, v___x_1587_);
    return v___x_1590_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1591_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7,
    );
    v___x_1592_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1593_ = lean_array_push(v___x_1592_, v___x_1591_);
    return v___x_1593_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1594_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5;
    v___x_1595_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8,
    );
    v___x_1596_ = lean_array_push(v___x_1595_, v___x_1594_);
    return v___x_1596_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1604_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__12;
    v___x_1605_ = l_Lean_mkAtom(v___x_1604_);
    return v___x_1605_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13,
    );
    v___x_1607_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1608_ = lean_array_push(v___x_1607_, v___x_1606_);
    return v___x_1608_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1621_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__17;
    v___x_1622_ = l_Lean_mkAtom(v___x_1621_);
    return v___x_1622_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1623_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19,
    );
    v___x_1624_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1625_ = lean_array_push(v___x_1624_, v___x_1623_);
    return v___x_1625_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1632_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5;
    v___x_1633_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1634_ = lean_array_push(v___x_1633_, v___x_1632_);
    return v___x_1634_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1635_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23,
    );
    v___x_1636_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22;
    v___x_1637_ = crate::leanh::lean_box(2);
    v___x_1638_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1638_, 0, v___x_1637_);
    crate::leanh::lean_ctor_set(v___x_1638_, 1, v___x_1636_);
    crate::leanh::lean_ctor_set(v___x_1638_, 2, v___x_1635_);
    return v___x_1638_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1639_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24,
    );
    v___x_1640_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20,
    );
    v___x_1641_ = lean_array_push(v___x_1640_, v___x_1639_);
    return v___x_1641_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1642_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5;
    v___x_1643_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25,
    );
    v___x_1644_ = lean_array_push(v___x_1643_, v___x_1642_);
    return v___x_1644_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1646_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__27;
    v___x_1647_ = l_Lean_mkAtom(v___x_1646_);
    return v___x_1647_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1648_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28,
    );
    v___x_1649_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1650_ = lean_array_push(v___x_1649_, v___x_1648_);
    return v___x_1650_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1651_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29,
    );
    v___x_1652_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
    v___x_1653_ = crate::leanh::lean_box(2);
    v___x_1654_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1654_, 0, v___x_1653_);
    crate::leanh::lean_ctor_set(v___x_1654_, 1, v___x_1652_);
    crate::leanh::lean_ctor_set(v___x_1654_, 2, v___x_1651_);
    return v___x_1654_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1655_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30,
    );
    v___x_1656_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26,
    );
    v___x_1657_ = lean_array_push(v___x_1656_, v___x_1655_);
    return v___x_1657_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1658_ = l_term_____x5b___x5d___closed__7;
    v___x_1659_ = l_Lean_mkAtom(v___x_1658_);
    return v___x_1659_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1660_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32,
    );
    v___x_1661_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1662_ = lean_array_push(v___x_1661_, v___x_1660_);
    return v___x_1662_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1669_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5;
    v___x_1670_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23,
    );
    v___x_1671_ = lean_array_push(v___x_1670_, v___x_1669_);
    return v___x_1671_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1672_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0;
    v___x_1673_ = lean_string_utf8_byte_size(v___x_1672_);
    return v___x_1673_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1674_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37,
    );
    v___x_1675_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1676_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0;
    v___x_1677_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1677_, 0, v___x_1676_);
    crate::leanh::lean_ctor_set(v___x_1677_, 1, v___x_1675_);
    crate::leanh::lean_ctor_set(v___x_1677_, 2, v___x_1674_);
    return v___x_1677_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1678_ = crate::leanh::lean_box(0);
    v___x_1679_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__2;
    v___x_1680_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38,
    );
    v___x_1681_ = crate::leanh::lean_box(2);
    v___x_1682_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1682_, 0, v___x_1681_);
    crate::leanh::lean_ctor_set(v___x_1682_, 1, v___x_1680_);
    crate::leanh::lean_ctor_set(v___x_1682_, 2, v___x_1679_);
    crate::leanh::lean_ctor_set(v___x_1682_, 3, v___x_1678_);
    return v___x_1682_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1683_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39,
    );
    v___x_1684_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36,
    );
    v___x_1685_ = lean_array_push(v___x_1684_, v___x_1683_);
    return v___x_1685_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1686_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40,
    );
    v___x_1687_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35;
    v___x_1688_ = crate::leanh::lean_box(2);
    v___x_1689_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1689_, 0, v___x_1688_);
    crate::leanh::lean_ctor_set(v___x_1689_, 1, v___x_1687_);
    crate::leanh::lean_ctor_set(v___x_1689_, 2, v___x_1686_);
    return v___x_1689_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1690_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41,
    );
    v___x_1691_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1692_ = lean_array_push(v___x_1691_, v___x_1690_);
    return v___x_1692_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1693_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42,
    );
    v___x_1694_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
    v___x_1695_ = crate::leanh::lean_box(2);
    v___x_1696_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1696_, 0, v___x_1695_);
    crate::leanh::lean_ctor_set(v___x_1696_, 1, v___x_1694_);
    crate::leanh::lean_ctor_set(v___x_1696_, 2, v___x_1693_);
    return v___x_1696_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1697_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43,
    );
    v___x_1698_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33,
    );
    v___x_1699_ = lean_array_push(v___x_1698_, v___x_1697_);
    return v___x_1699_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1700_ = l_term_____x5b___x5d___closed__17;
    v___x_1701_ = l_Lean_mkAtom(v___x_1700_);
    return v___x_1701_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1702_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45,
    );
    v___x_1703_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44,
    );
    v___x_1704_ = lean_array_push(v___x_1703_, v___x_1702_);
    return v___x_1704_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1705_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46,
    );
    v___x_1706_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
    v___x_1707_ = crate::leanh::lean_box(2);
    v___x_1708_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1708_, 0, v___x_1707_);
    crate::leanh::lean_ctor_set(v___x_1708_, 1, v___x_1706_);
    crate::leanh::lean_ctor_set(v___x_1708_, 2, v___x_1705_);
    return v___x_1708_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1709_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47,
    );
    v___x_1710_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31,
    );
    v___x_1711_ = lean_array_push(v___x_1710_, v___x_1709_);
    return v___x_1711_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1712_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5;
    v___x_1713_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48,
    );
    v___x_1714_ = lean_array_push(v___x_1713_, v___x_1712_);
    return v___x_1714_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1715_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49,
    );
    v___x_1716_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18;
    v___x_1717_ = crate::leanh::lean_box(2);
    v___x_1718_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1718_, 0, v___x_1717_);
    crate::leanh::lean_ctor_set(v___x_1718_, 1, v___x_1716_);
    crate::leanh::lean_ctor_set(v___x_1718_, 2, v___x_1715_);
    return v___x_1718_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1719_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50,
    );
    v___x_1720_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1721_ = lean_array_push(v___x_1720_, v___x_1719_);
    return v___x_1721_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1723_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__52;
    v___x_1724_ = l_Lean_mkAtom(v___x_1723_);
    return v___x_1724_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1725_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53,
    );
    v___x_1726_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51,
    );
    v___x_1727_ = lean_array_push(v___x_1726_, v___x_1725_);
    return v___x_1727_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1734_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55;
    v___x_1735_ = l_Lean_mkAtom(v___x_1734_);
    return v___x_1735_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1736_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57,
    );
    v___x_1737_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1738_ = lean_array_push(v___x_1737_, v___x_1736_);
    return v___x_1738_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1739_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5;
    v___x_1740_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58,
    );
    v___x_1741_ = lean_array_push(v___x_1740_, v___x_1739_);
    return v___x_1741_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1742_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59,
    );
    v___x_1743_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56;
    v___x_1744_ = crate::leanh::lean_box(2);
    v___x_1745_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1745_, 0, v___x_1744_);
    crate::leanh::lean_ctor_set(v___x_1745_, 1, v___x_1743_);
    crate::leanh::lean_ctor_set(v___x_1745_, 2, v___x_1742_);
    return v___x_1745_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1746_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60,
    );
    v___x_1747_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54,
    );
    v___x_1748_ = lean_array_push(v___x_1747_, v___x_1746_);
    return v___x_1748_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1749_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61,
    );
    v___x_1750_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16;
    v___x_1751_ = crate::leanh::lean_box(2);
    v___x_1752_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1752_, 0, v___x_1751_);
    crate::leanh::lean_ctor_set(v___x_1752_, 1, v___x_1750_);
    crate::leanh::lean_ctor_set(v___x_1752_, 2, v___x_1749_);
    return v___x_1752_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1753_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62,
    );
    v___x_1754_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1755_ = lean_array_push(v___x_1754_, v___x_1753_);
    return v___x_1755_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1756_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63,
    );
    v___x_1757_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
    v___x_1758_ = crate::leanh::lean_box(2);
    v___x_1759_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1759_, 0, v___x_1758_);
    crate::leanh::lean_ctor_set(v___x_1759_, 1, v___x_1757_);
    crate::leanh::lean_ctor_set(v___x_1759_, 2, v___x_1756_);
    return v___x_1759_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1760_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64,
    );
    v___x_1761_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1762_ = lean_array_push(v___x_1761_, v___x_1760_);
    return v___x_1762_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1763_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65,
    );
    v___x_1764_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32;
    v___x_1765_ = crate::leanh::lean_box(2);
    v___x_1766_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1766_, 0, v___x_1765_);
    crate::leanh::lean_ctor_set(v___x_1766_, 1, v___x_1764_);
    crate::leanh::lean_ctor_set(v___x_1766_, 2, v___x_1763_);
    return v___x_1766_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1767_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66,
    );
    v___x_1768_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1769_ = lean_array_push(v___x_1768_, v___x_1767_);
    return v___x_1769_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1770_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67,
    );
    v___x_1771_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30;
    v___x_1772_ = crate::leanh::lean_box(2);
    v___x_1773_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1773_, 0, v___x_1772_);
    crate::leanh::lean_ctor_set(v___x_1773_, 1, v___x_1771_);
    crate::leanh::lean_ctor_set(v___x_1773_, 2, v___x_1770_);
    return v___x_1773_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1774_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68,
    );
    v___x_1775_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14,
    );
    v___x_1776_ = lean_array_push(v___x_1775_, v___x_1774_);
    return v___x_1776_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69,
    );
    v___x_1778_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11;
    v___x_1779_ = crate::leanh::lean_box(2);
    v___x_1780_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1780_, 0, v___x_1779_);
    crate::leanh::lean_ctor_set(v___x_1780_, 1, v___x_1778_);
    crate::leanh::lean_ctor_set(v___x_1780_, 2, v___x_1777_);
    return v___x_1780_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1781_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70,
    );
    v___x_1782_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9,
    );
    v___x_1783_ = lean_array_push(v___x_1782_, v___x_1781_);
    return v___x_1783_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1784_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71,
    );
    v___x_1785_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
    v___x_1786_ = crate::leanh::lean_box(2);
    v___x_1787_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1787_, 0, v___x_1786_);
    crate::leanh::lean_ctor_set(v___x_1787_, 1, v___x_1785_);
    crate::leanh::lean_ctor_set(v___x_1787_, 2, v___x_1784_);
    return v___x_1787_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1788_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72,
    );
    v___x_1789_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1790_ = lean_array_push(v___x_1789_, v___x_1788_);
    return v___x_1790_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1791_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73,
    );
    v___x_1792_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32;
    v___x_1793_ = crate::leanh::lean_box(2);
    v___x_1794_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1794_, 0, v___x_1793_);
    crate::leanh::lean_ctor_set(v___x_1794_, 1, v___x_1792_);
    crate::leanh::lean_ctor_set(v___x_1794_, 2, v___x_1791_);
    return v___x_1794_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1795_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74,
    );
    v___x_1796_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1797_ = lean_array_push(v___x_1796_, v___x_1795_);
    return v___x_1797_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1798_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75,
    );
    v___x_1799_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30;
    v___x_1800_ = crate::leanh::lean_box(2);
    v___x_1801_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1801_, 0, v___x_1800_);
    crate::leanh::lean_ctor_set(v___x_1801_, 1, v___x_1799_);
    crate::leanh::lean_ctor_set(v___x_1801_, 2, v___x_1798_);
    return v___x_1801_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1802_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76,
    );
    return v___x_1802_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1803_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0;
    v___x_1804_ = lean_string_utf8_byte_size(v___x_1803_);
    return v___x_1804_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1805_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__0),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__0_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__0,
    );
    v___x_1806_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1807_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0;
    v___x_1808_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1808_, 0, v___x_1807_);
    crate::leanh::lean_ctor_set(v___x_1808_, 1, v___x_1806_);
    crate::leanh::lean_ctor_set(v___x_1808_, 2, v___x_1805_);
    return v___x_1808_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1809_ = crate::leanh::lean_box(0);
    v___x_1810_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__2;
    v___x_1811_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__1),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__1_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__1,
    );
    v___x_1812_ = crate::leanh::lean_box(2);
    v___x_1813_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1813_, 0, v___x_1812_);
    crate::leanh::lean_ctor_set(v___x_1813_, 1, v___x_1811_);
    crate::leanh::lean_ctor_set(v___x_1813_, 2, v___x_1810_);
    crate::leanh::lean_ctor_set(v___x_1813_, 3, v___x_1809_);
    return v___x_1813_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1814_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__2),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__2_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__2,
    );
    v___x_1815_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36,
    );
    v___x_1816_ = lean_array_push(v___x_1815_, v___x_1814_);
    return v___x_1816_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1817_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__3),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__3_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__3,
    );
    v___x_1818_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35;
    v___x_1819_ = crate::leanh::lean_box(2);
    v___x_1820_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1820_, 0, v___x_1819_);
    crate::leanh::lean_ctor_set(v___x_1820_, 1, v___x_1818_);
    crate::leanh::lean_ctor_set(v___x_1820_, 2, v___x_1817_);
    return v___x_1820_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1821_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__4),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__4_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__4,
    );
    v___x_1822_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1823_ = lean_array_push(v___x_1822_, v___x_1821_);
    return v___x_1823_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1825_ = l_LawfulGetElem_getElem_x21__def___autoParam___closed__6;
    v___x_1826_ = l_Lean_mkAtom(v___x_1825_);
    return v___x_1826_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1827_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__7),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__7_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__7,
    );
    v___x_1828_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__5),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__5_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__5,
    );
    v___x_1829_ = lean_array_push(v___x_1828_, v___x_1827_);
    return v___x_1829_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1830_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41,
    );
    v___x_1831_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__8),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__8_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__8,
    );
    v___x_1832_ = lean_array_push(v___x_1831_, v___x_1830_);
    return v___x_1832_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1833_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__7),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__7_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__7,
    );
    v___x_1834_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__9),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__9_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__9,
    );
    v___x_1835_ = lean_array_push(v___x_1834_, v___x_1833_);
    return v___x_1835_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1837_ = l_LawfulGetElem_getElem_x21__def___autoParam___closed__11;
    v___x_1838_ = lean_string_utf8_byte_size(v___x_1837_);
    return v___x_1838_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1839_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__12),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__12_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__12,
    );
    v___x_1840_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1841_ = l_LawfulGetElem_getElem_x21__def___autoParam___closed__11;
    v___x_1842_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1842_, 0, v___x_1841_);
    crate::leanh::lean_ctor_set(v___x_1842_, 1, v___x_1840_);
    crate::leanh::lean_ctor_set(v___x_1842_, 2, v___x_1839_);
    return v___x_1842_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1845_ = crate::leanh::lean_box(0);
    v___x_1846_ = l_LawfulGetElem_getElem_x21__def___autoParam___closed__14;
    v___x_1847_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__13),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__13_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__13,
    );
    v___x_1848_ = crate::leanh::lean_box(2);
    v___x_1849_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1849_, 0, v___x_1848_);
    crate::leanh::lean_ctor_set(v___x_1849_, 1, v___x_1847_);
    crate::leanh::lean_ctor_set(v___x_1849_, 2, v___x_1846_);
    crate::leanh::lean_ctor_set(v___x_1849_, 3, v___x_1845_);
    return v___x_1849_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1850_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__15),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__15_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__15,
    );
    v___x_1851_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36,
    );
    v___x_1852_ = lean_array_push(v___x_1851_, v___x_1850_);
    return v___x_1852_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1853_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__16),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__16_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__16,
    );
    v___x_1854_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35;
    v___x_1855_ = crate::leanh::lean_box(2);
    v___x_1856_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1856_, 0, v___x_1855_);
    crate::leanh::lean_ctor_set(v___x_1856_, 1, v___x_1854_);
    crate::leanh::lean_ctor_set(v___x_1856_, 2, v___x_1853_);
    return v___x_1856_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1857_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__17),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__17_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__17,
    );
    v___x_1858_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__10),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__10_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__10,
    );
    v___x_1859_ = lean_array_push(v___x_1858_, v___x_1857_);
    return v___x_1859_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1860_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__18),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__18_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__18,
    );
    v___x_1861_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
    v___x_1862_ = crate::leanh::lean_box(2);
    v___x_1863_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1863_, 0, v___x_1862_);
    crate::leanh::lean_ctor_set(v___x_1863_, 1, v___x_1861_);
    crate::leanh::lean_ctor_set(v___x_1863_, 2, v___x_1860_);
    return v___x_1863_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1864_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__19),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__19_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__19,
    );
    v___x_1865_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33,
    );
    v___x_1866_ = lean_array_push(v___x_1865_, v___x_1864_);
    return v___x_1866_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1867_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45,
    );
    v___x_1868_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__20),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__20_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__20,
    );
    v___x_1869_ = lean_array_push(v___x_1868_, v___x_1867_);
    return v___x_1869_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1870_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__21),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__21_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__21,
    );
    v___x_1871_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
    v___x_1872_ = crate::leanh::lean_box(2);
    v___x_1873_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1873_, 0, v___x_1872_);
    crate::leanh::lean_ctor_set(v___x_1873_, 1, v___x_1871_);
    crate::leanh::lean_ctor_set(v___x_1873_, 2, v___x_1870_);
    return v___x_1873_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1874_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__22),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__22_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__22,
    );
    v___x_1875_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31,
    );
    v___x_1876_ = lean_array_push(v___x_1875_, v___x_1874_);
    return v___x_1876_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1877_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5;
    v___x_1878_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__23),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__23_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__23,
    );
    v___x_1879_ = lean_array_push(v___x_1878_, v___x_1877_);
    return v___x_1879_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1880_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__24),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__24_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__24,
    );
    v___x_1881_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18;
    v___x_1882_ = crate::leanh::lean_box(2);
    v___x_1883_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1883_, 0, v___x_1882_);
    crate::leanh::lean_ctor_set(v___x_1883_, 1, v___x_1881_);
    crate::leanh::lean_ctor_set(v___x_1883_, 2, v___x_1880_);
    return v___x_1883_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1884_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__25),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__25_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__25,
    );
    v___x_1885_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9,
    );
    v___x_1886_ = lean_array_push(v___x_1885_, v___x_1884_);
    return v___x_1886_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1887_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__26),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__26_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__26,
    );
    v___x_1888_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
    v___x_1889_ = crate::leanh::lean_box(2);
    v___x_1890_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1890_, 0, v___x_1889_);
    crate::leanh::lean_ctor_set(v___x_1890_, 1, v___x_1888_);
    crate::leanh::lean_ctor_set(v___x_1890_, 2, v___x_1887_);
    return v___x_1890_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1891_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__27),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__27_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__27,
    );
    v___x_1892_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1893_ = lean_array_push(v___x_1892_, v___x_1891_);
    return v___x_1893_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__29()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1894_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__28),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__28_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__28,
    );
    v___x_1895_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32;
    v___x_1896_ = crate::leanh::lean_box(2);
    v___x_1897_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1897_, 0, v___x_1896_);
    crate::leanh::lean_ctor_set(v___x_1897_, 1, v___x_1895_);
    crate::leanh::lean_ctor_set(v___x_1897_, 2, v___x_1894_);
    return v___x_1897_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__30()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1898_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__29),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__29_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__29,
    );
    v___x_1899_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1900_ = lean_array_push(v___x_1899_, v___x_1898_);
    return v___x_1900_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1901_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__30),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__30_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__30,
    );
    v___x_1902_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30;
    v___x_1903_ = crate::leanh::lean_box(2);
    v___x_1904_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1904_, 0, v___x_1903_);
    crate::leanh::lean_ctor_set(v___x_1904_, 1, v___x_1902_);
    crate::leanh::lean_ctor_set(v___x_1904_, 2, v___x_1901_);
    return v___x_1904_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1905_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__31),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__31_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__31,
    );
    return v___x_1905_;
}
pub unsafe fn l___private_Init_GetElem_0__GetElem_x3f_match__1_splitter___redArg(
    mut v_x_1906_: *mut crate::leanh::LeanObject,
    mut v_h__1_1907_: *mut crate::leanh::LeanObject,
    mut v_h__2_1908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1906_) == 0 {
        let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1907_);
        v___x_1909_ = crate::leanh::lean_box(0);
        v___x_1910_ = crate::leanh::lean_apply_1(v_h__2_1908_, v___x_1909_);
        return v___x_1910_;
    } else {
        let mut v_val_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1908_);
        v_val_1911_ = crate::leanh::lean_ctor_get(v_x_1906_, 0);
        crate::leanh::lean_inc(v_val_1911_);
        crate::leanh::lean_dec_ref_known(v_x_1906_, 1);
        v___x_1912_ = crate::leanh::lean_apply_1(v_h__1_1907_, v_val_1911_);
        return v___x_1912_;
    }
}
pub unsafe fn l___private_Init_GetElem_0__GetElem_x3f_match__1_splitter(
    mut v_elem_1913_: *mut crate::leanh::LeanObject,
    mut v_motive_1914_: *mut crate::leanh::LeanObject,
    mut v_x_1915_: *mut crate::leanh::LeanObject,
    mut v_h__1_1916_: *mut crate::leanh::LeanObject,
    mut v_h__2_1917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1915_) == 0 {
        let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1916_);
        v___x_1918_ = crate::leanh::lean_box(0);
        v___x_1919_ = crate::leanh::lean_apply_1(v_h__2_1917_, v___x_1918_);
        return v___x_1919_;
    } else {
        let mut v_val_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1917_);
        v_val_1920_ = crate::leanh::lean_ctor_get(v_x_1915_, 0);
        crate::leanh::lean_inc(v_val_1920_);
        crate::leanh::lean_dec_ref_known(v_x_1915_, 1);
        v___x_1921_ = crate::leanh::lean_apply_1(v_h__1_1916_, v_val_1920_);
        return v___x_1921_;
    }
}
pub unsafe fn l_Fin_instGetElemFinVal___redArg___lam__0(
    mut v_inst_1922_: *mut crate::leanh::LeanObject,
    mut v_xs_1923_: *mut crate::leanh::LeanObject,
    mut v_i_1924_: *mut crate::leanh::LeanObject,
    mut v_h_1925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1926_ = crate::leanh::lean_apply_3(
        v_inst_1922_,
        v_xs_1923_,
        v_i_1924_,
        crate::leanh::lean_box(0),
    );
    return v___x_1926_;
}
pub unsafe fn l_Fin_instGetElemFinVal___redArg(
    mut v_inst_1927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1928_ = crate::leanh::lean_alloc_closure(
        l_Fin_instGetElemFinVal___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1928_, 0, v_inst_1927_);
    return v___f_1928_;
}
pub unsafe fn l_Fin_instGetElemFinVal(
    mut v_cont_1929_: *mut crate::leanh::LeanObject,
    mut v_elem_1930_: *mut crate::leanh::LeanObject,
    mut v_dom_1931_: *mut crate::leanh::LeanObject,
    mut v_n_1932_: *mut crate::leanh::LeanObject,
    mut v_inst_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1934_ = crate::leanh::lean_alloc_closure(
        l_Fin_instGetElemFinVal___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1934_, 0, v_inst_1933_);
    return v___f_1934_;
}
pub unsafe fn l_Fin_instGetElemFinVal___boxed(
    mut v_cont_1935_: *mut crate::leanh::LeanObject,
    mut v_elem_1936_: *mut crate::leanh::LeanObject,
    mut v_dom_1937_: *mut crate::leanh::LeanObject,
    mut v_n_1938_: *mut crate::leanh::LeanObject,
    mut v_inst_1939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1940_ = l_Fin_instGetElemFinVal(
        v_cont_1935_,
        v_elem_1936_,
        v_dom_1937_,
        v_n_1938_,
        v_inst_1939_,
    );
    crate::leanh::lean_dec(v_n_1938_);
    return v_res_1940_;
}
pub unsafe fn l_Fin_instGetElem_x3fFinVal___redArg___lam__0(
    mut v_getElem_x3f_1941_: *mut crate::leanh::LeanObject,
    mut v_xs_1942_: *mut crate::leanh::LeanObject,
    mut v_i_1943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1944_ = crate::leanh::lean_apply_2(v_getElem_x3f_1941_, v_xs_1942_, v_i_1943_);
    return v___x_1944_;
}
pub unsafe fn l_Fin_instGetElem_x3fFinVal___redArg___lam__1(
    mut v_getElem_x21_1945_: *mut crate::leanh::LeanObject,
    mut v_inst_1946_: *mut crate::leanh::LeanObject,
    mut v_xs_1947_: *mut crate::leanh::LeanObject,
    mut v_i_1948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1949_ =
        crate::leanh::lean_apply_3(v_getElem_x21_1945_, v_inst_1946_, v_xs_1947_, v_i_1948_);
    return v___x_1949_;
}
pub unsafe fn l_Fin_instGetElem_x3fFinVal___redArg(
    mut v_inst_1950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toGetElem_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getElem_x3f_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getElem_x21_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1956_: u8 = 0;
    let mut v___f_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1963_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toGetElem_1951_ = crate::leanh::lean_ctor_get(v_inst_1950_, 0);
                v_getElem_x3f_1952_ = crate::leanh::lean_ctor_get(v_inst_1950_, 1);
                v_getElem_x21_1953_ = crate::leanh::lean_ctor_get(v_inst_1950_, 2);
                v_isSharedCheck_1963_ = (!crate::leanh::lean_is_exclusive(v_inst_1950_)) as u8;
                if v_isSharedCheck_1963_ == 0 {
                    v___x_1955_ = v_inst_1950_;
                    v_isShared_1956_ = v_isSharedCheck_1963_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_getElem_x21_1953_);
                    crate::leanh::lean_inc(v_getElem_x3f_1952_);
                    crate::leanh::lean_inc(v_toGetElem_1951_);
                    crate::leanh::lean_dec(v_inst_1950_);
                    v___x_1955_ = crate::leanh::lean_box(0);
                    v_isShared_1956_ = v_isSharedCheck_1963_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1957_ = crate::leanh::lean_alloc_closure(
                    l_Fin_instGetElem_x3fFinVal___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1957_, 0, v_getElem_x3f_1952_);
                v___f_1958_ = crate::leanh::lean_alloc_closure(
                    l_Fin_instGetElem_x3fFinVal___redArg___lam__1 as *mut core::ffi::c_void,
                    4,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1958_, 0, v_getElem_x21_1953_);
                v___f_1959_ = crate::leanh::lean_alloc_closure(
                    l_Fin_instGetElemFinVal___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1959_, 0, v_toGetElem_1951_);
                if v_isShared_1956_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1955_, 2, v___f_1958_);
                    crate::leanh::lean_ctor_set(v___x_1955_, 1, v___f_1957_);
                    crate::leanh::lean_ctor_set(v___x_1955_, 0, v___f_1959_);
                    v___x_1961_ = v___x_1955_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1962_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___f_1959_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 1, v___f_1957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 2, v___f_1958_);
                    v___x_1961_ = v_reuseFailAlloc_1962_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1961_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Fin_instGetElem_x3fFinVal(
    mut v_cont_1964_: *mut crate::leanh::LeanObject,
    mut v_elem_1965_: *mut crate::leanh::LeanObject,
    mut v_dom_1966_: *mut crate::leanh::LeanObject,
    mut v_n_1967_: *mut crate::leanh::LeanObject,
    mut v_inst_1968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1969_ = l_Fin_instGetElem_x3fFinVal___redArg(v_inst_1968_);
    return v___x_1969_;
}
pub unsafe fn l_Fin_instGetElem_x3fFinVal___boxed(
    mut v_cont_1970_: *mut crate::leanh::LeanObject,
    mut v_elem_1971_: *mut crate::leanh::LeanObject,
    mut v_dom_1972_: *mut crate::leanh::LeanObject,
    mut v_n_1973_: *mut crate::leanh::LeanObject,
    mut v_inst_1974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1975_ = l_Fin_instGetElem_x3fFinVal(
        v_cont_1970_,
        v_elem_1971_,
        v_dom_1972_,
        v_n_1973_,
        v_inst_1974_,
    );
    crate::leanh::lean_dec(v_n_1973_);
    return v_res_1975_;
}
pub unsafe fn _init_l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2004_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__10;
    v___x_2005_ = l_String_toRawSubstring_x27(v___x_2004_);
    return v___x_2005_;
}
pub unsafe fn l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1(
    mut v_x_2025_: *mut crate::leanh::LeanObject,
    mut v_a_2026_: *mut crate::leanh::LeanObject,
    mut v_a_2027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: u8 = 0;
    v___x_2028_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__1;
    v___x_2029_ = l_Lean_Syntax_isOfKind(v_x_2025_, v___x_2028_);
    if v___x_2029_ == 0 {
        let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2030_ = crate::leanh::lean_box(1);
        v___x_2031_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2031_, 0, v___x_2030_);
        crate::leanh::lean_ctor_set(v___x_2031_, 1, v_a_2027_);
        return v___x_2031_;
    } else {
        let mut v_quotContext_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2035_: u8 = 0;
        let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2032_ = crate::leanh::lean_ctor_get(v_a_2026_, 1);
        v_currMacroScope_2033_ = crate::leanh::lean_ctor_get(v_a_2026_, 2);
        v_ref_2034_ = crate::leanh::lean_ctor_get(v_a_2026_, 5);
        v___x_2035_ = 0;
        v___x_2036_ = l_Lean_SourceInfo_fromRef(v_ref_2034_, v___x_2035_);
        v___x_2037_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3;
        v___x_2038_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
        v___x_2039_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4;
        v___x_2040_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__18;
        crate::leanh::lean_inc_n(v___x_2036_, 20);
        v___x_2041_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2041_, 0, v___x_2036_);
        crate::leanh::lean_ctor_set(v___x_2041_, 1, v___x_2040_);
        v___x_2042_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30;
        v___x_2043_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32;
        v___x_2044_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6;
        v___x_2045_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__7;
        v___x_2046_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2046_, 0, v___x_2036_);
        crate::leanh::lean_ctor_set(v___x_2046_, 1, v___x_2045_);
        v___x_2047_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__8;
        v___x_2048_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9;
        v___x_2049_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2049_, 0, v___x_2036_);
        crate::leanh::lean_ctor_set(v___x_2049_, 1, v___x_2047_);
        v___x_2050_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11), core::ptr::addr_of_mut!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_once), _init_l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11);
        v___x_2051_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14;
        crate::leanh::lean_inc(v_currMacroScope_2033_);
        crate::leanh::lean_inc(v_quotContext_2032_);
        v___x_2052_ =
            l_Lean_addMacroScope(v_quotContext_2032_, v___x_2051_, v_currMacroScope_2033_);
        v___x_2053_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__16;
        v___x_2054_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2054_, 0, v___x_2036_);
        crate::leanh::lean_ctor_set(v___x_2054_, 1, v___x_2050_);
        crate::leanh::lean_ctor_set(v___x_2054_, 2, v___x_2052_);
        crate::leanh::lean_ctor_set(v___x_2054_, 3, v___x_2053_);
        v___x_2055_ = l_Lean_Syntax_node2(v___x_2036_, v___x_2048_, v___x_2049_, v___x_2054_);
        v___x_2056_ = l_Lean_Syntax_node1(v___x_2036_, v___x_2038_, v___x_2055_);
        v___x_2057_ = l_Lean_Syntax_node1(v___x_2036_, v___x_2043_, v___x_2056_);
        v___x_2058_ = l_Lean_Syntax_node1(v___x_2036_, v___x_2042_, v___x_2057_);
        v___x_2059_ = l_Lean_Syntax_node2(v___x_2036_, v___x_2044_, v___x_2046_, v___x_2058_);
        v___x_2060_ = l_Lean_Syntax_node1(v___x_2036_, v___x_2038_, v___x_2059_);
        v___x_2061_ = l_Lean_Syntax_node1(v___x_2036_, v___x_2043_, v___x_2060_);
        v___x_2062_ = l_Lean_Syntax_node1(v___x_2036_, v___x_2042_, v___x_2061_);
        v___x_2063_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__36;
        v___x_2064_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2064_, 0, v___x_2036_);
        crate::leanh::lean_ctor_set(v___x_2064_, 1, v___x_2063_);
        v___x_2065_ = l_Lean_Syntax_node3(
            v___x_2036_,
            v___x_2039_,
            v___x_2041_,
            v___x_2062_,
            v___x_2064_,
        );
        v___x_2066_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__17;
        v___x_2067_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2067_, 0, v___x_2036_);
        crate::leanh::lean_ctor_set(v___x_2067_, 1, v___x_2066_);
        v___x_2068_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__18;
        v___x_2069_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2069_, 0, v___x_2036_);
        crate::leanh::lean_ctor_set(v___x_2069_, 1, v___x_2068_);
        v___x_2070_ = l_Lean_Syntax_node1(v___x_2036_, v___x_2028_, v___x_2069_);
        v___x_2071_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__19;
        v___x_2072_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20;
        v___x_2073_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2073_, 0, v___x_2036_);
        crate::leanh::lean_ctor_set(v___x_2073_, 1, v___x_2071_);
        v___x_2074_ = l_Lean_Syntax_node1(v___x_2036_, v___x_2072_, v___x_2073_);
        crate::leanh::lean_inc_ref(v___x_2067_);
        v___x_2075_ = l_Lean_Syntax_node5(
            v___x_2036_,
            v___x_2038_,
            v___x_2065_,
            v___x_2067_,
            v___x_2070_,
            v___x_2067_,
            v___x_2074_,
        );
        v___x_2076_ = l_Lean_Syntax_node1(v___x_2036_, v___x_2037_, v___x_2075_);
        v___x_2077_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2077_, 0, v___x_2076_);
        crate::leanh::lean_ctor_set(v___x_2077_, 1, v_a_2027_);
        return v___x_2077_;
    }
}
pub unsafe fn l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___boxed(
    mut v_x_2078_: *mut crate::leanh::LeanObject,
    mut v_a_2079_: *mut crate::leanh::LeanObject,
    mut v_a_2080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2081_ =
        l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1(
            v_x_2078_, v_a_2079_, v_a_2080_,
        );
    crate::leanh::lean_dec_ref(v_a_2079_);
    return v_res_2081_;
}
pub unsafe fn l_List_instGetElemNatLtLength___lam__0(
    mut v_as_2082_: *mut crate::leanh::LeanObject,
    mut v_i_2083_: *mut crate::leanh::LeanObject,
    mut v_h_2084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2085_ = l_List_get___redArg(v_as_2082_, v_i_2083_);
    return v___x_2085_;
}
pub unsafe fn l_List_instGetElemNatLtLength___lam__0___boxed(
    mut v_as_2086_: *mut crate::leanh::LeanObject,
    mut v_i_2087_: *mut crate::leanh::LeanObject,
    mut v_h_2088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2089_ = l_List_instGetElemNatLtLength___lam__0(v_as_2086_, v_i_2087_, v_h_2088_);
    crate::leanh::lean_dec(v_as_2086_);
    return v_res_2089_;
}
pub unsafe fn l_List_instGetElemNatLtLength(
    mut v_00_u03b1_2091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2092_ = l_List_instGetElemNatLtLength___closed__0;
    return v___f_2092_;
}
pub unsafe fn l_List_get_x3fInternal___redArg(
    mut v_x_2093_: *mut crate::leanh::LeanObject,
    mut v_x_2094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2098_: u8 = 0;
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2093_) == 1 {
                    v_head_2095_ = crate::leanh::lean_ctor_get(v_x_2093_, 0);
                    v_tail_2096_ = crate::leanh::lean_ctor_get(v_x_2093_, 1);
                    v_zero_2097_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_isZero_2098_ = lean_nat_dec_eq(v_x_2094_, v_zero_2097_);
                    if v_isZero_2098_ == 1 {
                        crate::leanh::lean_dec(v_x_2094_);
                        crate::leanh::lean_inc(v_head_2095_);
                        v___x_2099_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2099_, 0, v_head_2095_);
                        return v___x_2099_;
                    } else {
                        v_one_2100_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_n_2101_ = lean_nat_sub(v_x_2094_, v_one_2100_);
                        crate::leanh::lean_dec(v_x_2094_);
                        v_x_2093_ = v_tail_2096_;
                        v_x_2094_ = v_n_2101_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_2094_);
                    v___x_2103_ = crate::leanh::lean_box(0);
                    return v___x_2103_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_get_x3fInternal___redArg___boxed(
    mut v_x_2104_: *mut crate::leanh::LeanObject,
    mut v_x_2105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2106_ = l_List_get_x3fInternal___redArg(v_x_2104_, v_x_2105_);
    crate::leanh::lean_dec(v_x_2104_);
    return v_res_2106_;
}
pub unsafe fn l_List_get_x3fInternal(
    mut v_00_u03b1_2107_: *mut crate::leanh::LeanObject,
    mut v_x_2108_: *mut crate::leanh::LeanObject,
    mut v_x_2109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2110_ = l_List_get_x3fInternal___redArg(v_x_2108_, v_x_2109_);
    return v___x_2110_;
}
pub unsafe fn l_List_get_x3fInternal___boxed(
    mut v_00_u03b1_2111_: *mut crate::leanh::LeanObject,
    mut v_x_2112_: *mut crate::leanh::LeanObject,
    mut v_x_2113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2114_ = l_List_get_x3fInternal(v_00_u03b1_2111_, v_x_2112_, v_x_2113_);
    crate::leanh::lean_dec(v_x_2112_);
    return v_res_2114_;
}
pub unsafe fn l_List_get_x21Internal___redArg(
    mut v_inst_2117_: *mut crate::leanh::LeanObject,
    mut v_x_2118_: *mut crate::leanh::LeanObject,
    mut v_x_2119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2123_: u8 = 0;
    let mut v_one_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2118_) == 1 {
                    v_head_2120_ = crate::leanh::lean_ctor_get(v_x_2118_, 0);
                    v_tail_2121_ = crate::leanh::lean_ctor_get(v_x_2118_, 1);
                    v_zero_2122_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_isZero_2123_ = lean_nat_dec_eq(v_x_2119_, v_zero_2122_);
                    if v_isZero_2123_ == 1 {
                        crate::leanh::lean_dec(v_x_2119_);
                        crate::leanh::lean_inc(v_head_2120_);
                        return v_head_2120_;
                    } else {
                        v_one_2124_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_n_2125_ = lean_nat_sub(v_x_2119_, v_one_2124_);
                        crate::leanh::lean_dec(v_x_2119_);
                        v_x_2118_ = v_tail_2121_;
                        v_x_2119_ = v_n_2125_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_2119_);
                    v___x_2127_ = l_outOfBounds___redArg___closed__0;
                    v___x_2128_ = l_List_get_x21Internal___redArg___closed__0;
                    v___x_2129_ = crate::leanh::lean_unsigned_to_nat(332);
                    v___x_2130_ = crate::leanh::lean_unsigned_to_nat(18);
                    v___x_2131_ = l_List_get_x21Internal___redArg___closed__1;
                    v___x_2132_ = l_mkPanicMessageWithDecl(
                        v___x_2127_,
                        v___x_2128_,
                        v___x_2129_,
                        v___x_2130_,
                        v___x_2131_,
                    );
                    v___x_2133_ = l_panic___redArg(v_inst_2117_, v___x_2132_);
                    return v___x_2133_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_get_x21Internal___redArg___boxed(
    mut v_inst_2134_: *mut crate::leanh::LeanObject,
    mut v_x_2135_: *mut crate::leanh::LeanObject,
    mut v_x_2136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2137_ = l_List_get_x21Internal___redArg(v_inst_2134_, v_x_2135_, v_x_2136_);
    crate::leanh::lean_dec(v_x_2135_);
    crate::leanh::lean_dec(v_inst_2134_);
    return v_res_2137_;
}
pub unsafe fn l_List_get_x21Internal(
    mut v_00_u03b1_2138_: *mut crate::leanh::LeanObject,
    mut v_inst_2139_: *mut crate::leanh::LeanObject,
    mut v_x_2140_: *mut crate::leanh::LeanObject,
    mut v_x_2141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2142_ = l_List_get_x21Internal___redArg(v_inst_2139_, v_x_2140_, v_x_2141_);
    return v___x_2142_;
}
pub unsafe fn l_List_get_x21Internal___boxed(
    mut v_00_u03b1_2143_: *mut crate::leanh::LeanObject,
    mut v_inst_2144_: *mut crate::leanh::LeanObject,
    mut v_x_2145_: *mut crate::leanh::LeanObject,
    mut v_x_2146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2147_ = l_List_get_x21Internal(v_00_u03b1_2143_, v_inst_2144_, v_x_2145_, v_x_2146_);
    crate::leanh::lean_dec(v_x_2145_);
    crate::leanh::lean_dec(v_inst_2144_);
    return v_res_2147_;
}
pub unsafe fn l_List_instGetElem_x3fNatLtLength(
    mut v_00_u03b1_2154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2155_ = l_List_instGetElem_x3fNatLtLength___closed__2;
    return v___x_2155_;
}
pub unsafe fn l_Array_instGetElemNatLtSize___lam__0(
    mut v_xs_2156_: *mut crate::leanh::LeanObject,
    mut v_i_2157_: *mut crate::leanh::LeanObject,
    mut v_h_2158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2159_ = lean_array_fget_borrowed(v_xs_2156_, v_i_2157_);
    crate::leanh::lean_inc(v___x_2159_);
    return v___x_2159_;
}
pub unsafe fn l_Array_instGetElemNatLtSize___lam__0___boxed(
    mut v_xs_2160_: *mut crate::leanh::LeanObject,
    mut v_i_2161_: *mut crate::leanh::LeanObject,
    mut v_h_2162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2163_ = l_Array_instGetElemNatLtSize___lam__0(v_xs_2160_, v_i_2161_, v_h_2162_);
    crate::leanh::lean_dec(v_i_2161_);
    crate::leanh::lean_dec_ref(v_xs_2160_);
    return v_res_2163_;
}
pub unsafe fn l_Array_instGetElemNatLtSize(
    mut v_00_u03b1_2165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2166_ = l_Array_instGetElemNatLtSize___closed__0;
    return v___f_2166_;
}
pub unsafe fn l_Array_instGetElem_x3fNatLtSize___lam__0(
    mut v_xs_2167_: *mut crate::leanh::LeanObject,
    mut v_i_2168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: u8 = 0;
    v___x_2169_ = lean_array_get_size(v_xs_2167_);
    v___x_2170_ = lean_nat_dec_lt(v_i_2168_, v___x_2169_);
    if v___x_2170_ == 0 {
        let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2171_ = crate::leanh::lean_box(0);
        return v___x_2171_;
    } else {
        let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2172_ = lean_array_fget_borrowed(v_xs_2167_, v_i_2168_);
        crate::leanh::lean_inc(v___x_2172_);
        v___x_2173_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2173_, 0, v___x_2172_);
        return v___x_2173_;
    }
}
pub unsafe fn l_Array_instGetElem_x3fNatLtSize___lam__0___boxed(
    mut v_xs_2174_: *mut crate::leanh::LeanObject,
    mut v_i_2175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2176_ = l_Array_instGetElem_x3fNatLtSize___lam__0(v_xs_2174_, v_i_2175_);
    crate::leanh::lean_dec(v_i_2175_);
    crate::leanh::lean_dec_ref(v_xs_2174_);
    return v_res_2176_;
}
pub unsafe fn l_Array_instGetElem_x3fNatLtSize___lam__1(
    mut v_inst_2177_: *mut crate::leanh::LeanObject,
    mut v_xs_2178_: *mut crate::leanh::LeanObject,
    mut v_i_2179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2180_ = lean_array_get_borrowed(v_inst_2177_, v_xs_2178_, v_i_2179_);
    crate::leanh::lean_inc(v___x_2180_);
    return v___x_2180_;
}
pub unsafe fn l_Array_instGetElem_x3fNatLtSize___lam__1___boxed(
    mut v_inst_2181_: *mut crate::leanh::LeanObject,
    mut v_xs_2182_: *mut crate::leanh::LeanObject,
    mut v_i_2183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2184_ = l_Array_instGetElem_x3fNatLtSize___lam__1(v_inst_2181_, v_xs_2182_, v_i_2183_);
    crate::leanh::lean_dec(v_i_2183_);
    crate::leanh::lean_dec_ref(v_xs_2182_);
    crate::leanh::lean_dec(v_inst_2181_);
    return v_res_2184_;
}
pub unsafe fn l_Array_instGetElem_x3fNatLtSize(
    mut v_00_u03b1_2191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2192_ = l_Array_instGetElem_x3fNatLtSize___closed__2;
    return v___x_2192_;
}
pub unsafe fn l_Lean_Syntax_instGetElemNatTrue___lam__0(
    mut v_stx_2193_: *mut crate::leanh::LeanObject,
    mut v_i_2194_: *mut crate::leanh::LeanObject,
    mut v_x_2195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2196_ = l_Lean_Syntax_getArg(v_stx_2193_, v_i_2194_);
    return v___x_2196_;
}
pub unsafe fn l_Lean_Syntax_instGetElemNatTrue___lam__0___boxed(
    mut v_stx_2197_: *mut crate::leanh::LeanObject,
    mut v_i_2198_: *mut crate::leanh::LeanObject,
    mut v_x_2199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2200_ = l_Lean_Syntax_instGetElemNatTrue___lam__0(v_stx_2197_, v_i_2198_, v_x_2199_);
    crate::leanh::lean_dec(v_i_2198_);
    crate::leanh::lean_dec(v_stx_2197_);
    return v_res_2200_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_GetElem(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_GetElem(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_LawfulGetElem_getElem_x3f__def___autoParam =
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam();
    crate::leanh::lean_mark_persistent(l_LawfulGetElem_getElem_x3f__def___autoParam);
    l_LawfulGetElem_getElem_x21__def___autoParam =
        _init_l_LawfulGetElem_getElem_x21__def___autoParam();
    crate::leanh::lean_mark_persistent(l_LawfulGetElem_getElem_x21__def___autoParam);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_GetElem(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_GetElem(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_GetElem(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_GetElem(builtin);
}
