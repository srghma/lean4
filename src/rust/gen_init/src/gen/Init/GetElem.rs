// Lean compiler output
// Module: Init.GetElem
// Imports: Init.Util Init.Data.Option.Basic
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_string_utf8_byte_size,
};
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
pub static l_outOfBounds___redArg___closed__0_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_outOfBounds___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_outOfBounds___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_outOfBounds___redArg___closed__1_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_outOfBounds___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_outOfBounds___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_outOfBounds___redArg___closed__2_value: leanh::LeanStringObject<20> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_outOfBounds___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_outOfBounds___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__0_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_term_____x5b___x5d___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__0_value) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__0_value)
                as *mut leanh::LeanObject,
            17746073143502587047 as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__1_value) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__2_value: leanh::LeanStringObject<8> =
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
static mut l_term_____x5b___x5d___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__2_value) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__2_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__4_value: leanh::LeanStringObject<5> =
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
        m_data: [110, 111, 87, 115, 0],
    };
static mut l_term_____x5b___x5d___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__4_value) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__4_value)
                as *mut leanh::LeanObject,
            1581446985683836252 as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__5_value) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__6_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(l_term_____x5b___x5d___closed__5_value)
            as *mut leanh::LeanObject],
    };
static mut l_term_____x5b___x5d___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__6_value) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__7_value: leanh::LeanStringObject<2> =
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
static mut l_term_____x5b___x5d___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__7_value) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__8_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_term_____x5b___x5d___closed__7_value)
            as *mut leanh::LeanObject],
    };
static mut l_term_____x5b___x5d___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__8_value) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__9_value) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__10_value: leanh::LeanStringObject<16> =
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
static mut l_term_____x5b___x5d___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__10_value) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__11_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__10_value)
                as *mut leanh::LeanObject,
            1164644006045091397 as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__11_value) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__12_value: leanh::LeanStringObject<5> =
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
static mut l_term_____x5b___x5d___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__12_value) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__13_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__12_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__13_value) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__14_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__13_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__14_value) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__15_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__11_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__15_value) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__16_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__16_value) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__17_value: leanh::LeanStringObject<2> =
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
static mut l_term_____x5b___x5d___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__17_value) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__18_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_term_____x5b___x5d___closed__17_value)
            as *mut leanh::LeanObject],
    };
static mut l_term_____x5b___x5d___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__18_value) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__19_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__16_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__18_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__19_value) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___closed__20_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__19_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__20_value) as *mut leanh::LeanObject;
pub static mut l_term_____x5b___x5d: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___closed__20_value) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__2_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__2_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__3_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__3_value
) as *mut leanh::LeanObject;
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__2_value
        ) as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__3_value
        ) as *mut leanh::LeanObject,
        12966880221525079621 as *mut leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5_value
) as *mut leanh::LeanObject;
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__7_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5_value
        ) as *mut leanh::LeanObject,
        18081053125345290886 as *mut leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__7_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__8_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__8_value
) as *mut leanh::LeanObject;
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__9_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__8_value
        ) as *mut leanh::LeanObject,
        854136310249810287 as *mut leanh::LeanObject,
    ],
};
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__9_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__9_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5_value
        ) as *mut leanh::LeanObject,
        8801718159307809986 as *mut leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__9_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__10_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__9_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__10_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__11_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__10_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__11_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__12_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__12_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__12_value
        ) as *mut leanh::LeanObject,
        9855511589286918680 as *mut leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__14_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__14_value
) as *mut leanh::LeanObject;
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__2_value
        ) as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__14_value
        ) as *mut leanh::LeanObject,
        7932075773091973500 as *mut leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__16_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__16_value
) as *mut leanh::LeanObject;
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__2_value
        ) as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__16_value
        ) as *mut leanh::LeanObject,
        7306243862518720553 as *mut leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__18_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__18_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__19_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__19_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__20_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__19_value
        ) as *mut leanh::LeanObject,
        9871775667037945883 as *mut leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__20:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__20_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__21_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__21_value
) as *mut leanh::LeanObject;
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__23_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__23:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__23_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__24_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__23_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__24:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__24_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__25_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__25_value
) as *mut leanh::LeanObject;
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__2_value
        ) as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__25_value
        ) as *mut leanh::LeanObject,
        16173796135615239867 as *mut leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__27_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__27_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__29_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__29_value
) as *mut leanh::LeanObject;
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value
        ) as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__29_value
        ) as *mut leanh::LeanObject,
        8504843326314613972 as *mut leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__31_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__31_value
) as *mut leanh::LeanObject;
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value
        ) as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__31_value
        ) as *mut leanh::LeanObject,
        17228437386856258271 as *mut leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__33_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__33_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__34_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__33_value
        ) as *mut leanh::LeanObject,
        3731765604234633101 as *mut leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__34:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__34_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__35_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
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
        103, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116, 105, 99, 0,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__35:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__35_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__36_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__36_value
) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d_x27___00__closed__0_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_term_____x5b___x5d_x27___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__0_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d_x27___00__closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__0_value)
                as *mut leanh::LeanObject,
            14552850886997009045 as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d_x27___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d_x27___00__closed__2_value: leanh::LeanStringObject<3> =
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
        m_data: [93, 39, 0],
    };
static mut l_term_____x5b___x5d_x27___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d_x27___00__closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d_x27___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d_x27___00__closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__16_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d_x27___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d_x27___00__closed__5_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__13_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d_x27___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d_x27___00__closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d_x27___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d_x27___00__closed__7_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d_x27___00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__7_value)
        as *mut leanh::LeanObject;
pub static mut l_term_____x5b___x5d_x27__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d_x27___00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__0_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_term_____x5b___x5d___x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__0_value)
                as *mut leanh::LeanObject,
            1231705503909655209 as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__2_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_term_____x5b___x5d___x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__2_value)
                as *mut leanh::LeanObject,
            2214559063752339918 as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x3f___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__4_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x3f___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x3f___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x3f___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__18_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x3f___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__8_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x3f___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__9_value: leanh::LeanStringObject<2> =
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
        m_data: [63, 0],
    };
static mut l_term_____x5b___x5d___x3f___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__10_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x3f___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__11_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x3f___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___x3f___closed__12_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x3f___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__12_value)
        as *mut leanh::LeanObject;
pub static mut l_term_____x5b___x5d___x3f: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__12_value)
        as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0_value
) as *mut leanh::LeanObject;
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__2_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0_value
        ) as *mut leanh::LeanObject,
        12289893685329059214 as *mut leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__2_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__3_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__3_value
) as *mut leanh::LeanObject;
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__3_value) as *mut leanh::LeanObject,1284173141442213452 as *mut leanh::LeanObject] };
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0_value) as *mut leanh::LeanObject,14790288273250445109 as *mut leanh::LeanObject] };
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__4_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__5_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__4_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__5_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__6_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__5_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__6_value
) as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___x21___closed__0_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_term_____x5b___x5d___x21___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___x21___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__0_value)
                as *mut leanh::LeanObject,
            941824322364543252 as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x21___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___x21___closed__2_value: leanh::LeanStringObject<2> =
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
        m_data: [33, 0],
    };
static mut l_term_____x5b___x5d___x21___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___x21___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x21___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___x21___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_term_____x5b___x5d___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___x3f___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x21___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_term_____x5b___x5d___x21___closed__5_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_term_____x5b___x5d___x21___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_term_____x5b___x5d___x21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_term_____x5b___x5d___x21___closed__5_value)
        as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0_value
) as *mut leanh::LeanObject;
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__2_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0_value
        ) as *mut leanh::LeanObject,
        14784475134464642716 as *mut leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__2_value
) as *mut leanh::LeanObject;
static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__3_value) as *mut leanh::LeanObject,1284173141442213452 as *mut leanh::LeanObject] };
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0_value) as *mut leanh::LeanObject,16409410464876292983 as *mut leanh::LeanObject] };
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__3_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__4_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__3_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__4_value
) as *mut leanh::LeanObject;
pub static l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__5_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__4_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__5_value
) as *mut leanh::LeanObject;
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__1_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__1_value)
        as *mut leanh::LeanObject;
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value
        ) as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__1_value)
            as *mut leanh::LeanObject,
        3278676588586250010 as *mut leanh::LeanObject,
    ],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 1,
    },
    m_objs: [
        (((2 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__10_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__10_value)
        as *mut leanh::LeanObject;
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value
        ) as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__10_value)
            as *mut leanh::LeanObject,
        10962186005905108258 as *mut leanh::LeanObject,
    ],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__12_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__15_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__15_value)
        as *mut leanh::LeanObject;
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value
        ) as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__15_value)
            as *mut leanh::LeanObject,
        12695378809397736991 as *mut leanh::LeanObject,
    ],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__17_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__17_value)
        as *mut leanh::LeanObject;
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value
        ) as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__17_value)
            as *mut leanh::LeanObject,
        12783917532758215986 as *mut leanh::LeanObject,
    ],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18_value)
        as *mut leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__21_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__21_value)
        as *mut leanh::LeanObject;
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value
        ) as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__21_value)
            as *mut leanh::LeanObject,
        3488656302031949961 as *mut leanh::LeanObject,
    ],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22_value)
        as *mut leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__27_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__27_value)
        as *mut leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__34_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__34_value)
        as *mut leanh::LeanObject;
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value
        ) as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__34_value)
            as *mut leanh::LeanObject,
        7383208167966365478 as *mut leanh::LeanObject,
    ],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35_value)
        as *mut leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__52_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__52_value)
        as *mut leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55_value)
        as *mut leanh::LeanObject;
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value
        ) as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55_value)
            as *mut leanh::LeanObject,
        7757010358911522857 as *mut leanh::LeanObject,
    ],
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56_value)
        as *mut leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_LawfulGetElem_getElem_x3f__def___autoParam: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_LawfulGetElem_getElem_x21__def___autoParam___closed__6_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
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
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_LawfulGetElem_getElem_x21__def___autoParam___closed__11_value:
    leanh::LeanStringObject<23> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_LawfulGetElem_getElem_x21__def___autoParam___closed__14_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__11_value)
            as *mut leanh::LeanObject,
        4748755860924891891 as *mut leanh::LeanObject,
    ],
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__16:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__18:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__20:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__21_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__21:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__22_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__22:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__23_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__23:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__24_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__24:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__25_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__25:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__26_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__26:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__27_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__27:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__28_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__28:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__29_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__29:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__30_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__30:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__31_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulGetElem_getElem_x21__def___autoParam___closed__31:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_LawfulGetElem_getElem_x21__def___autoParam: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value: leanh::LeanStringObject<33> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [116, 97, 99, 116, 105, 99, 71, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116, 105, 99, 95, 101, 120, 116, 101, 110, 115, 105, 98, 108, 101, 0]};
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value) as *mut leanh::LeanObject,7705027380931481693 as *mut leanh::LeanObject] };
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 101, 113, 49, 0]};
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut leanh::LeanObject;
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value) as *mut leanh::LeanObject,8471002125274025202 as *mut leanh::LeanObject] };
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value) as *mut leanh::LeanObject;
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__14_value) as *mut leanh::LeanObject,8689124066155232629 as *mut leanh::LeanObject] };
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [119, 105, 116, 104, 82, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value) as *mut leanh::LeanObject;
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value) as *mut leanh::LeanObject,6022092293134036165 as *mut leanh::LeanObject] };
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [119, 105, 116, 104, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 112, 112, 108, 121, 0]};
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value) as *mut leanh::LeanObject;
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value) as *mut leanh::LeanObject,5826123769708379594 as *mut leanh::LeanObject] };
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [70, 105, 110, 46, 118, 97, 108, 95, 108, 116, 95, 111, 102, 95, 108, 101, 0]};
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value) as *mut leanh::LeanObject;
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [70, 105, 110, 0]};
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [118, 97, 108, 95, 108, 116, 95, 111, 102, 95, 108, 101, 0]};
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value) as *mut leanh::LeanObject;
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value) as *mut leanh::LeanObject,15815496672699636542 as *mut leanh::LeanObject] };
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value) as *mut leanh::LeanObject,11955149997473870394 as *mut leanh::LeanObject] };
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value) as *mut leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value) as *mut leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value) as *mut leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [103, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116, 105, 99, 95, 101, 120, 116, 101, 110, 115, 105, 98, 108, 101, 0]};
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value) as *mut leanh::LeanObject;
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 111, 110, 101, 0]};
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value) as *mut leanh::LeanObject;
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__28_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__19_value) as *mut leanh::LeanObject,8876691400619696497 as *mut leanh::LeanObject] };
static mut l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20_value) as *mut leanh::LeanObject;
pub static l_List_instGetElemNatLtLength___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_List_instGetElemNatLtLength___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_List_instGetElemNatLtLength___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_instGetElemNatLtLength___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_List_get_x21Internal___redArg___closed__0_value: leanh::LeanStringObject<18> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_List_get_x21Internal___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_get_x21Internal___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_List_get_x21Internal___redArg___closed__1_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_List_get_x21Internal___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_get_x21Internal___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_List_instGetElem_x3fNatLtLength___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_List_get_x3fInternal___redArg___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_List_instGetElem_x3fNatLtLength___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_instGetElem_x3fNatLtLength___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_List_instGetElem_x3fNatLtLength___closed__1_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_List_get_x21Internal___redArg___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_List_instGetElem_x3fNatLtLength___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_instGetElem_x3fNatLtLength___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_List_instGetElem_x3fNatLtLength___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_List_instGetElemNatLtLength___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_instGetElem_x3fNatLtLength___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_instGetElem_x3fNatLtLength___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_List_instGetElem_x3fNatLtLength___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_instGetElem_x3fNatLtLength___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Array_instGetElemNatLtSize___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Array_instGetElemNatLtSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_instGetElemNatLtSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_instGetElemNatLtSize___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Array_instGetElem_x3fNatLtSize___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Array_instGetElem_x3fNatLtSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_instGetElem_x3fNatLtSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_instGetElem_x3fNatLtSize___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Array_instGetElem_x3fNatLtSize___closed__1_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Array_instGetElem_x3fNatLtSize___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_instGetElem_x3fNatLtSize___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_instGetElem_x3fNatLtSize___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Array_instGetElem_x3fNatLtSize___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_instGetElemNatLtSize___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_instGetElem_x3fNatLtSize___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_instGetElem_x3fNatLtSize___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_instGetElem_x3fNatLtSize___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_instGetElem_x3fNatLtSize___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_instGetElemNatTrue___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Syntax_instGetElemNatTrue___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Syntax_instGetElemNatTrue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instGetElemNatTrue___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Syntax_instGetElemNatTrue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instGetElemNatTrue___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_outOfBounds___redArg(
    mut v_inst_1105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1106_ = l_outOfBounds___redArg___closed__0;
    v___x_1107_ = l_outOfBounds___redArg___closed__1;
    v___x_1108_ = leanh::lean_unsigned_to_nat(18);
    v___x_1109_ = leanh::lean_unsigned_to_nat(2);
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
    mut v_inst_1113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1114_ = l_outOfBounds___redArg(v_inst_1113_);
    leanh::lean_dec(v_inst_1113_);
    return v_res_1114_;
}
pub unsafe fn l_outOfBounds(
    mut v_00_u03b1_1115_: *mut leanh::LeanObject,
    mut v_inst_1116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1117_ = l_outOfBounds___redArg(v_inst_1116_);
    return v___x_1117_;
}
pub unsafe fn l_outOfBounds___boxed(
    mut v_00_u03b1_1118_: *mut leanh::LeanObject,
    mut v_inst_1119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1120_ = l_outOfBounds(v_00_u03b1_1118_, v_inst_1119_);
    leanh::lean_dec(v_inst_1119_);
    return v_res_1120_;
}
pub unsafe fn _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1178_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__5;
    v___x_1179_ = l_String_toRawSubstring_x27(v___x_1178_);
    return v___x_1179_;
}
pub unsafe fn _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1212_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__21;
    v___x_1213_ = l_String_toRawSubstring_x27(v___x_1212_);
    return v___x_1213_;
}
pub unsafe fn l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1(
    mut v_x_1244_: *mut leanh::LeanObject,
    mut v_a_1245_: *mut leanh::LeanObject,
    mut v_a_1246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: u8 = 0;
    v___x_1247_ = l_term_____x5b___x5d___closed__1;
    leanh::lean_inc(v_x_1244_);
    v___x_1248_ = l_Lean_Syntax_isOfKind(v_x_1244_, v___x_1247_);
    if v___x_1248_ == 0 {
        let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1244_);
        v___x_1249_ = leanh::lean_box(1);
        v___x_1250_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1250_, 0, v___x_1249_);
        leanh::lean_ctor_set(v___x_1250_, 1, v_a_1246_);
        return v___x_1250_;
    } else {
        let mut v_quotContext_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1258_: u8 = 0;
        let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1251_ = leanh::lean_ctor_get(v_a_1245_, 1);
        v_currMacroScope_1252_ = leanh::lean_ctor_get(v_a_1245_, 2);
        v_ref_1253_ = leanh::lean_ctor_get(v_a_1245_, 5);
        v___x_1254_ = leanh::lean_unsigned_to_nat(0);
        v___x_1255_ = l_Lean_Syntax_getArg(v_x_1244_, v___x_1254_);
        v___x_1256_ = leanh::lean_unsigned_to_nat(2);
        v___x_1257_ = l_Lean_Syntax_getArg(v_x_1244_, v___x_1256_);
        leanh::lean_dec(v_x_1244_);
        v___x_1258_ = 0;
        v___x_1259_ = l_Lean_SourceInfo_fromRef(v_ref_1253_, v___x_1258_);
        v___x_1260_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4;
        v___x_1261_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6_once
            ),
            _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6,
        );
        v___x_1262_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__7;
        leanh::lean_inc_n(v_currMacroScope_1252_, 2);
        leanh::lean_inc_n(v_quotContext_1251_, 2);
        v___x_1263_ =
            l_Lean_addMacroScope(v_quotContext_1251_, v___x_1262_, v_currMacroScope_1252_);
        v___x_1264_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__11;
        leanh::lean_inc_n(v___x_1259_, 15);
        v___x_1265_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1265_, 0, v___x_1259_);
        leanh::lean_ctor_set(v___x_1265_, 1, v___x_1261_);
        leanh::lean_ctor_set(v___x_1265_, 2, v___x_1263_);
        leanh::lean_ctor_set(v___x_1265_, 3, v___x_1264_);
        v___x_1266_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
        v___x_1267_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__15;
        v___x_1268_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__17;
        v___x_1269_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__18;
        v___x_1270_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1270_, 0, v___x_1259_);
        leanh::lean_ctor_set(v___x_1270_, 1, v___x_1269_);
        v___x_1271_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__20;
        v___x_1272_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22_once
            ),
            _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__22,
        );
        v___x_1273_ = leanh::lean_box(0);
        v___x_1274_ =
            l_Lean_addMacroScope(v_quotContext_1251_, v___x_1273_, v_currMacroScope_1252_);
        v___x_1275_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__24;
        v___x_1276_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1276_, 0, v___x_1259_);
        leanh::lean_ctor_set(v___x_1276_, 1, v___x_1272_);
        leanh::lean_ctor_set(v___x_1276_, 2, v___x_1274_);
        leanh::lean_ctor_set(v___x_1276_, 3, v___x_1275_);
        v___x_1277_ = l_Lean_Syntax_node1(v___x_1259_, v___x_1271_, v___x_1276_);
        v___x_1278_ = l_Lean_Syntax_node2(v___x_1259_, v___x_1268_, v___x_1270_, v___x_1277_);
        v___x_1279_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__26;
        v___x_1280_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__27;
        v___x_1281_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1281_, 0, v___x_1259_);
        leanh::lean_ctor_set(v___x_1281_, 1, v___x_1280_);
        v___x_1282_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30;
        v___x_1283_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32;
        v___x_1284_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__34;
        v___x_1285_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__35;
        v___x_1286_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1286_, 0, v___x_1259_);
        leanh::lean_ctor_set(v___x_1286_, 1, v___x_1285_);
        v___x_1287_ = l_Lean_Syntax_node1(v___x_1259_, v___x_1284_, v___x_1286_);
        v___x_1288_ = l_Lean_Syntax_node1(v___x_1259_, v___x_1266_, v___x_1287_);
        v___x_1289_ = l_Lean_Syntax_node1(v___x_1259_, v___x_1283_, v___x_1288_);
        v___x_1290_ = l_Lean_Syntax_node1(v___x_1259_, v___x_1282_, v___x_1289_);
        v___x_1291_ = l_Lean_Syntax_node2(v___x_1259_, v___x_1279_, v___x_1281_, v___x_1290_);
        v___x_1292_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__36;
        v___x_1293_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1293_, 0, v___x_1259_);
        leanh::lean_ctor_set(v___x_1293_, 1, v___x_1292_);
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
        v___x_1297_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1297_, 0, v___x_1296_);
        leanh::lean_ctor_set(v___x_1297_, 1, v_a_1246_);
        return v___x_1297_;
    }
}
pub unsafe fn l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___boxed(
    mut v_x_1298_: *mut leanh::LeanObject,
    mut v_a_1299_: *mut leanh::LeanObject,
    mut v_a_1300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1301_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1(
        v_x_1298_, v_a_1299_, v_a_1300_,
    );
    leanh::lean_dec_ref(v_a_1299_);
    return v_res_1301_;
}
pub unsafe fn l___aux__Init__GetElem______macroRules__term_____x5b___x5d_x27____1(
    mut v_x_1325_: *mut leanh::LeanObject,
    mut v_a_1326_: *mut leanh::LeanObject,
    mut v_a_1327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: u8 = 0;
    v___x_1328_ = l_term_____x5b___x5d_x27___00__closed__1;
    leanh::lean_inc(v_x_1325_);
    v___x_1329_ = l_Lean_Syntax_isOfKind(v_x_1325_, v___x_1328_);
    if v___x_1329_ == 0 {
        let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1325_);
        v___x_1330_ = leanh::lean_box(1);
        v___x_1331_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1331_, 0, v___x_1330_);
        leanh::lean_ctor_set(v___x_1331_, 1, v_a_1327_);
        return v___x_1331_;
    } else {
        let mut v_quotContext_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1341_: u8 = 0;
        let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1332_ = leanh::lean_ctor_get(v_a_1326_, 1);
        v_currMacroScope_1333_ = leanh::lean_ctor_get(v_a_1326_, 2);
        v_ref_1334_ = leanh::lean_ctor_get(v_a_1326_, 5);
        v___x_1335_ = leanh::lean_unsigned_to_nat(0);
        v___x_1336_ = l_Lean_Syntax_getArg(v_x_1325_, v___x_1335_);
        v___x_1337_ = leanh::lean_unsigned_to_nat(2);
        v___x_1338_ = l_Lean_Syntax_getArg(v_x_1325_, v___x_1337_);
        v___x_1339_ = leanh::lean_unsigned_to_nat(4);
        v___x_1340_ = l_Lean_Syntax_getArg(v_x_1325_, v___x_1339_);
        leanh::lean_dec(v_x_1325_);
        v___x_1341_ = 0;
        v___x_1342_ = l_Lean_SourceInfo_fromRef(v_ref_1334_, v___x_1341_);
        v___x_1343_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4;
        v___x_1344_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6
            ),
            core::ptr::addr_of_mut!(
                l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6_once
            ),
            _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__6,
        );
        v___x_1345_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__7;
        leanh::lean_inc(v_currMacroScope_1333_);
        leanh::lean_inc(v_quotContext_1332_);
        v___x_1346_ =
            l_Lean_addMacroScope(v_quotContext_1332_, v___x_1345_, v_currMacroScope_1333_);
        v___x_1347_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__11;
        leanh::lean_inc_n(v___x_1342_, 2);
        v___x_1348_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1348_, 0, v___x_1342_);
        leanh::lean_ctor_set(v___x_1348_, 1, v___x_1344_);
        leanh::lean_ctor_set(v___x_1348_, 2, v___x_1346_);
        leanh::lean_ctor_set(v___x_1348_, 3, v___x_1347_);
        v___x_1349_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
        v___x_1350_ = l_Lean_Syntax_node3(
            v___x_1342_,
            v___x_1349_,
            v___x_1336_,
            v___x_1338_,
            v___x_1340_,
        );
        v___x_1351_ = l_Lean_Syntax_node2(v___x_1342_, v___x_1343_, v___x_1348_, v___x_1350_);
        v___x_1352_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1352_, 0, v___x_1351_);
        leanh::lean_ctor_set(v___x_1352_, 1, v_a_1327_);
        return v___x_1352_;
    }
}
pub unsafe fn l___aux__Init__GetElem______macroRules__term_____x5b___x5d_x27____1___boxed(
    mut v_x_1353_: *mut leanh::LeanObject,
    mut v_a_1354_: *mut leanh::LeanObject,
    mut v_a_1355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1356_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d_x27____1(
        v_x_1353_, v_a_1354_, v_a_1355_,
    );
    leanh::lean_dec_ref(v_a_1354_);
    return v_res_1356_;
}
pub unsafe fn l_decidableGetElem_x3f___redArg(
    mut v_inst_1357_: *mut leanh::LeanObject,
    mut v_xs_1358_: *mut leanh::LeanObject,
    mut v_i_1359_: *mut leanh::LeanObject,
    mut v_inst_1360_: u8,
) -> *mut leanh::LeanObject {
    if v_inst_1360_ == 0 {
        let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_i_1359_);
        leanh::lean_dec(v_xs_1358_);
        leanh::lean_dec(v_inst_1357_);
        v___x_1361_ = leanh::lean_box(0);
        return v___x_1361_;
    } else {
        let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1362_ = leanh::lean_apply_3(
            v_inst_1357_,
            v_xs_1358_,
            v_i_1359_,
            leanh::lean_box(0),
        );
        v___x_1363_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1363_, 0, v___x_1362_);
        return v___x_1363_;
    }
}
pub unsafe fn l_decidableGetElem_x3f___redArg___boxed(
    mut v_inst_1364_: *mut leanh::LeanObject,
    mut v_xs_1365_: *mut leanh::LeanObject,
    mut v_i_1366_: *mut leanh::LeanObject,
    mut v_inst_1367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inst_16__boxed_1368_: u8 = 0;
    let mut v_res_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_inst_16__boxed_1368_ = (leanh::lean_unbox(v_inst_1367_) as u8);
    v_res_1369_ = l_decidableGetElem_x3f___redArg(
        v_inst_1364_,
        v_xs_1365_,
        v_i_1366_,
        v_inst_16__boxed_1368_,
    );
    return v_res_1369_;
}
pub unsafe fn l_decidableGetElem_x3f(
    mut v_coll_1370_: *mut leanh::LeanObject,
    mut v_idx_1371_: *mut leanh::LeanObject,
    mut v_elem_1372_: *mut leanh::LeanObject,
    mut v_valid_1373_: *mut leanh::LeanObject,
    mut v_inst_1374_: *mut leanh::LeanObject,
    mut v_xs_1375_: *mut leanh::LeanObject,
    mut v_i_1376_: *mut leanh::LeanObject,
    mut v_inst_1377_: u8,
) -> *mut leanh::LeanObject {
    if v_inst_1377_ == 0 {
        let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_i_1376_);
        leanh::lean_dec(v_xs_1375_);
        leanh::lean_dec(v_inst_1374_);
        v___x_1378_ = leanh::lean_box(0);
        return v___x_1378_;
    } else {
        let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1379_ = leanh::lean_apply_3(
            v_inst_1374_,
            v_xs_1375_,
            v_i_1376_,
            leanh::lean_box(0),
        );
        v___x_1380_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1380_, 0, v___x_1379_);
        return v___x_1380_;
    }
}
pub unsafe fn l_decidableGetElem_x3f___boxed(
    mut v_coll_1381_: *mut leanh::LeanObject,
    mut v_idx_1382_: *mut leanh::LeanObject,
    mut v_elem_1383_: *mut leanh::LeanObject,
    mut v_valid_1384_: *mut leanh::LeanObject,
    mut v_inst_1385_: *mut leanh::LeanObject,
    mut v_xs_1386_: *mut leanh::LeanObject,
    mut v_i_1387_: *mut leanh::LeanObject,
    mut v_inst_1388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inst_28__boxed_1389_: u8 = 0;
    let mut v_res_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_inst_28__boxed_1389_ = (leanh::lean_unbox(v_inst_1388_) as u8);
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
-> *mut leanh::LeanObject {
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1430_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0;
    v___x_1431_ = l_String_toRawSubstring_x27(v___x_1430_);
    return v___x_1431_;
}
pub unsafe fn l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1(
    mut v_x_1444_: *mut leanh::LeanObject,
    mut v_a_1445_: *mut leanh::LeanObject,
    mut v_a_1446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: u8 = 0;
    v___x_1447_ = l_term_____x5b___x5d___x3f___closed__1;
    leanh::lean_inc(v_x_1444_);
    v___x_1448_ = l_Lean_Syntax_isOfKind(v_x_1444_, v___x_1447_);
    if v___x_1448_ == 0 {
        let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1444_);
        v___x_1449_ = leanh::lean_box(1);
        v___x_1450_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1450_, 0, v___x_1449_);
        leanh::lean_ctor_set(v___x_1450_, 1, v_a_1446_);
        return v___x_1450_;
    } else {
        let mut v_quotContext_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1458_: u8 = 0;
        let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1451_ = leanh::lean_ctor_get(v_a_1445_, 1);
        v_currMacroScope_1452_ = leanh::lean_ctor_get(v_a_1445_, 2);
        v_ref_1453_ = leanh::lean_ctor_get(v_a_1445_, 5);
        v___x_1454_ = leanh::lean_unsigned_to_nat(0);
        v___x_1455_ = l_Lean_Syntax_getArg(v_x_1444_, v___x_1454_);
        v___x_1456_ = leanh::lean_unsigned_to_nat(3);
        v___x_1457_ = l_Lean_Syntax_getArg(v_x_1444_, v___x_1456_);
        leanh::lean_dec(v_x_1444_);
        v___x_1458_ = 0;
        v___x_1459_ = l_Lean_SourceInfo_fromRef(v_ref_1453_, v___x_1458_);
        v___x_1460_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4;
        v___x_1461_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1), core::ptr::addr_of_mut!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1_once), _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__1);
        v___x_1462_ =
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__2;
        leanh::lean_inc(v_currMacroScope_1452_);
        leanh::lean_inc(v_quotContext_1451_);
        v___x_1463_ =
            l_Lean_addMacroScope(v_quotContext_1451_, v___x_1462_, v_currMacroScope_1452_);
        v___x_1464_ =
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__6;
        leanh::lean_inc_n(v___x_1459_, 2);
        v___x_1465_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1465_, 0, v___x_1459_);
        leanh::lean_ctor_set(v___x_1465_, 1, v___x_1461_);
        leanh::lean_ctor_set(v___x_1465_, 2, v___x_1463_);
        leanh::lean_ctor_set(v___x_1465_, 3, v___x_1464_);
        v___x_1466_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
        v___x_1467_ = l_Lean_Syntax_node2(v___x_1459_, v___x_1466_, v___x_1455_, v___x_1457_);
        v___x_1468_ = l_Lean_Syntax_node2(v___x_1459_, v___x_1460_, v___x_1465_, v___x_1467_);
        v___x_1469_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1469_, 0, v___x_1468_);
        leanh::lean_ctor_set(v___x_1469_, 1, v_a_1446_);
        return v___x_1469_;
    }
}
pub unsafe fn l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___boxed(
    mut v_x_1470_: *mut leanh::LeanObject,
    mut v_a_1471_: *mut leanh::LeanObject,
    mut v_a_1472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1473_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1(
        v_x_1470_, v_a_1471_, v_a_1472_,
    );
    leanh::lean_dec_ref(v_a_1471_);
    return v_res_1473_;
}
pub unsafe fn _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1491_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0;
    v___x_1492_ = l_String_toRawSubstring_x27(v___x_1491_);
    return v___x_1492_;
}
pub unsafe fn l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1(
    mut v_x_1504_: *mut leanh::LeanObject,
    mut v_a_1505_: *mut leanh::LeanObject,
    mut v_a_1506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: u8 = 0;
    v___x_1507_ = l_term_____x5b___x5d___x21___closed__1;
    leanh::lean_inc(v_x_1504_);
    v___x_1508_ = l_Lean_Syntax_isOfKind(v_x_1504_, v___x_1507_);
    if v___x_1508_ == 0 {
        let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1504_);
        v___x_1509_ = leanh::lean_box(1);
        v___x_1510_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1510_, 0, v___x_1509_);
        leanh::lean_ctor_set(v___x_1510_, 1, v_a_1506_);
        return v___x_1510_;
    } else {
        let mut v_quotContext_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1518_: u8 = 0;
        let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1511_ = leanh::lean_ctor_get(v_a_1505_, 1);
        v_currMacroScope_1512_ = leanh::lean_ctor_get(v_a_1505_, 2);
        v_ref_1513_ = leanh::lean_ctor_get(v_a_1505_, 5);
        v___x_1514_ = leanh::lean_unsigned_to_nat(0);
        v___x_1515_ = l_Lean_Syntax_getArg(v_x_1504_, v___x_1514_);
        v___x_1516_ = leanh::lean_unsigned_to_nat(3);
        v___x_1517_ = l_Lean_Syntax_getArg(v_x_1504_, v___x_1516_);
        leanh::lean_dec(v_x_1504_);
        v___x_1518_ = 0;
        v___x_1519_ = l_Lean_SourceInfo_fromRef(v_ref_1513_, v___x_1518_);
        v___x_1520_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__4;
        v___x_1521_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1), core::ptr::addr_of_mut!(l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1_once), _init_l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__1);
        v___x_1522_ =
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__2;
        leanh::lean_inc(v_currMacroScope_1512_);
        leanh::lean_inc(v_quotContext_1511_);
        v___x_1523_ =
            l_Lean_addMacroScope(v_quotContext_1511_, v___x_1522_, v_currMacroScope_1512_);
        v___x_1524_ =
            l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__5;
        leanh::lean_inc_n(v___x_1519_, 2);
        v___x_1525_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1525_, 0, v___x_1519_);
        leanh::lean_ctor_set(v___x_1525_, 1, v___x_1521_);
        leanh::lean_ctor_set(v___x_1525_, 2, v___x_1523_);
        leanh::lean_ctor_set(v___x_1525_, 3, v___x_1524_);
        v___x_1526_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
        v___x_1527_ = l_Lean_Syntax_node2(v___x_1519_, v___x_1526_, v___x_1515_, v___x_1517_);
        v___x_1528_ = l_Lean_Syntax_node2(v___x_1519_, v___x_1520_, v___x_1525_, v___x_1527_);
        v___x_1529_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1529_, 0, v___x_1528_);
        leanh::lean_ctor_set(v___x_1529_, 1, v_a_1506_);
        return v___x_1529_;
    }
}
pub unsafe fn l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___boxed(
    mut v_x_1530_: *mut leanh::LeanObject,
    mut v_a_1531_: *mut leanh::LeanObject,
    mut v_a_1532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1533_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1(
        v_x_1530_, v_a_1531_, v_a_1532_,
    );
    leanh::lean_dec_ref(v_a_1531_);
    return v_res_1533_;
}
pub unsafe fn l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__0(
    mut v_inst_1534_: *mut leanh::LeanObject,
    mut v_inst_1535_: *mut leanh::LeanObject,
    mut v_xs_1536_: *mut leanh::LeanObject,
    mut v_i_1537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: u8 = 0;
    leanh::lean_inc(v_i_1537_);
    leanh::lean_inc(v_xs_1536_);
    v___x_1538_ = leanh::lean_apply_2(v_inst_1534_, v_xs_1536_, v_i_1537_);
    v___x_1539_ = (leanh::lean_unbox(v___x_1538_) as u8);
    if v___x_1539_ == 0 {
        let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_i_1537_);
        leanh::lean_dec(v_xs_1536_);
        leanh::lean_dec(v_inst_1535_);
        v___x_1540_ = leanh::lean_box(0);
        return v___x_1540_;
    } else {
        let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1541_ = leanh::lean_apply_3(
            v_inst_1535_,
            v_xs_1536_,
            v_i_1537_,
            leanh::lean_box(0),
        );
        v___x_1542_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1542_, 0, v___x_1541_);
        return v___x_1542_;
    }
}
pub unsafe fn l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1(
    mut v___f_1543_: *mut leanh::LeanObject,
    mut v_inst_1544_: *mut leanh::LeanObject,
    mut v_xs_1545_: *mut leanh::LeanObject,
    mut v_i_1546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1547_ = leanh::lean_apply_2(v___f_1543_, v_xs_1545_, v_i_1546_);
    if leanh::lean_obj_tag(v___x_1547_) == 0 {
        let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1548_ = l_outOfBounds___redArg(v_inst_1544_);
        return v___x_1548_;
    } else {
        let mut v_val_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1549_ = leanh::lean_ctor_get(v___x_1547_, 0);
        leanh::lean_inc(v_val_1549_);
        leanh::lean_dec_ref_known(v___x_1547_, 1);
        return v_val_1549_;
    }
}
pub unsafe fn l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1___boxed(
    mut v___f_1550_: *mut leanh::LeanObject,
    mut v_inst_1551_: *mut leanh::LeanObject,
    mut v_xs_1552_: *mut leanh::LeanObject,
    mut v_i_1553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1554_ = l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1(
        v___f_1550_,
        v_inst_1551_,
        v_xs_1552_,
        v_i_1553_,
    );
    leanh::lean_dec(v_inst_1551_);
    return v_res_1554_;
}
pub unsafe fn l_instGetElem_x3fOfGetElemOfDecidable___redArg(
    mut v_inst_1555_: *mut leanh::LeanObject,
    mut v_inst_1556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_inst_1555_);
    v___f_1557_ = leanh::lean_alloc_closure(
        l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_1557_, 0, v_inst_1556_);
    leanh::lean_closure_set(v___f_1557_, 1, v_inst_1555_);
    leanh::lean_inc_ref(v___f_1557_);
    v___f_1558_ = leanh::lean_alloc_closure(
        l_instGetElem_x3fOfGetElemOfDecidable___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1558_, 0, v___f_1557_);
    v___x_1559_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1559_, 0, v_inst_1555_);
    leanh::lean_ctor_set(v___x_1559_, 1, v___f_1557_);
    leanh::lean_ctor_set(v___x_1559_, 2, v___f_1558_);
    return v___x_1559_;
}
pub unsafe fn l_instGetElem_x3fOfGetElemOfDecidable(
    mut v_coll_1560_: *mut leanh::LeanObject,
    mut v_idx_1561_: *mut leanh::LeanObject,
    mut v_elem_1562_: *mut leanh::LeanObject,
    mut v_valid_1563_: *mut leanh::LeanObject,
    mut v_inst_1564_: *mut leanh::LeanObject,
    mut v_inst_1565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1566_ = l_instGetElem_x3fOfGetElemOfDecidable___redArg(v_inst_1564_, v_inst_1565_);
    return v___x_1566_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1575_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__1;
    v___x_1576_ = l_Lean_mkAtom(v___x_1575_);
    return v___x_1576_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1577_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__3,
    );
    v___x_1578_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1579_ = lean_array_push(v___x_1578_, v___x_1577_);
    return v___x_1579_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1584_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5;
    v___x_1585_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__4,
    );
    v___x_1586_ = lean_array_push(v___x_1585_, v___x_1584_);
    return v___x_1586_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1587_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__6,
    );
    v___x_1588_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__2;
    v___x_1589_ = leanh::lean_box(2);
    v___x_1590_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1590_, 0, v___x_1589_);
    leanh::lean_ctor_set(v___x_1590_, 1, v___x_1588_);
    leanh::lean_ctor_set(v___x_1590_, 2, v___x_1587_);
    return v___x_1590_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1591_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__7,
    );
    v___x_1592_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1593_ = lean_array_push(v___x_1592_, v___x_1591_);
    return v___x_1593_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1594_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5;
    v___x_1595_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__8,
    );
    v___x_1596_ = lean_array_push(v___x_1595_, v___x_1594_);
    return v___x_1596_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1604_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__12;
    v___x_1605_ = l_Lean_mkAtom(v___x_1604_);
    return v___x_1605_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__13,
    );
    v___x_1607_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1608_ = lean_array_push(v___x_1607_, v___x_1606_);
    return v___x_1608_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1621_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__17;
    v___x_1622_ = l_Lean_mkAtom(v___x_1621_);
    return v___x_1622_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1623_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__19,
    );
    v___x_1624_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1625_ = lean_array_push(v___x_1624_, v___x_1623_);
    return v___x_1625_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1632_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5;
    v___x_1633_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1634_ = lean_array_push(v___x_1633_, v___x_1632_);
    return v___x_1634_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1635_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23,
    );
    v___x_1636_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__22;
    v___x_1637_ = leanh::lean_box(2);
    v___x_1638_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1638_, 0, v___x_1637_);
    leanh::lean_ctor_set(v___x_1638_, 1, v___x_1636_);
    leanh::lean_ctor_set(v___x_1638_, 2, v___x_1635_);
    return v___x_1638_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1639_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__24,
    );
    v___x_1640_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__20,
    );
    v___x_1641_ = lean_array_push(v___x_1640_, v___x_1639_);
    return v___x_1641_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1642_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5;
    v___x_1643_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__25,
    );
    v___x_1644_ = lean_array_push(v___x_1643_, v___x_1642_);
    return v___x_1644_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28()
-> *mut leanh::LeanObject {
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1646_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__27;
    v___x_1647_ = l_Lean_mkAtom(v___x_1646_);
    return v___x_1647_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29()
-> *mut leanh::LeanObject {
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1648_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__28,
    );
    v___x_1649_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1650_ = lean_array_push(v___x_1649_, v___x_1648_);
    return v___x_1650_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30()
-> *mut leanh::LeanObject {
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1651_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__29,
    );
    v___x_1652_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
    v___x_1653_ = leanh::lean_box(2);
    v___x_1654_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1654_, 0, v___x_1653_);
    leanh::lean_ctor_set(v___x_1654_, 1, v___x_1652_);
    leanh::lean_ctor_set(v___x_1654_, 2, v___x_1651_);
    return v___x_1654_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31()
-> *mut leanh::LeanObject {
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1655_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__30,
    );
    v___x_1656_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__26,
    );
    v___x_1657_ = lean_array_push(v___x_1656_, v___x_1655_);
    return v___x_1657_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32()
-> *mut leanh::LeanObject {
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1658_ = l_term_____x5b___x5d___closed__7;
    v___x_1659_ = l_Lean_mkAtom(v___x_1658_);
    return v___x_1659_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33()
-> *mut leanh::LeanObject {
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1660_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__32,
    );
    v___x_1661_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1662_ = lean_array_push(v___x_1661_, v___x_1660_);
    return v___x_1662_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36()
-> *mut leanh::LeanObject {
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1669_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5;
    v___x_1670_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__23,
    );
    v___x_1671_ = lean_array_push(v___x_1670_, v___x_1669_);
    return v___x_1671_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37()
-> *mut leanh::LeanObject {
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1672_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0;
    v___x_1673_ = lean_string_utf8_byte_size(v___x_1672_);
    return v___x_1673_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38()
-> *mut leanh::LeanObject {
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1674_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__37,
    );
    v___x_1675_ = leanh::lean_unsigned_to_nat(0);
    v___x_1676_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__0;
    v___x_1677_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1677_, 0, v___x_1676_);
    leanh::lean_ctor_set(v___x_1677_, 1, v___x_1675_);
    leanh::lean_ctor_set(v___x_1677_, 2, v___x_1674_);
    return v___x_1677_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39()
-> *mut leanh::LeanObject {
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1678_ = leanh::lean_box(0);
    v___x_1679_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x3f__1___closed__2;
    v___x_1680_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__38,
    );
    v___x_1681_ = leanh::lean_box(2);
    v___x_1682_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1682_, 0, v___x_1681_);
    leanh::lean_ctor_set(v___x_1682_, 1, v___x_1680_);
    leanh::lean_ctor_set(v___x_1682_, 2, v___x_1679_);
    leanh::lean_ctor_set(v___x_1682_, 3, v___x_1678_);
    return v___x_1682_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40()
-> *mut leanh::LeanObject {
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1683_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__39,
    );
    v___x_1684_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36,
    );
    v___x_1685_ = lean_array_push(v___x_1684_, v___x_1683_);
    return v___x_1685_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41()
-> *mut leanh::LeanObject {
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1686_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__40,
    );
    v___x_1687_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35;
    v___x_1688_ = leanh::lean_box(2);
    v___x_1689_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1689_, 0, v___x_1688_);
    leanh::lean_ctor_set(v___x_1689_, 1, v___x_1687_);
    leanh::lean_ctor_set(v___x_1689_, 2, v___x_1686_);
    return v___x_1689_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42()
-> *mut leanh::LeanObject {
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1690_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41,
    );
    v___x_1691_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1692_ = lean_array_push(v___x_1691_, v___x_1690_);
    return v___x_1692_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43()
-> *mut leanh::LeanObject {
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1693_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__42,
    );
    v___x_1694_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
    v___x_1695_ = leanh::lean_box(2);
    v___x_1696_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1696_, 0, v___x_1695_);
    leanh::lean_ctor_set(v___x_1696_, 1, v___x_1694_);
    leanh::lean_ctor_set(v___x_1696_, 2, v___x_1693_);
    return v___x_1696_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44()
-> *mut leanh::LeanObject {
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1697_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__43,
    );
    v___x_1698_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33,
    );
    v___x_1699_ = lean_array_push(v___x_1698_, v___x_1697_);
    return v___x_1699_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45()
-> *mut leanh::LeanObject {
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1700_ = l_term_____x5b___x5d___closed__17;
    v___x_1701_ = l_Lean_mkAtom(v___x_1700_);
    return v___x_1701_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46()
-> *mut leanh::LeanObject {
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1702_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45,
    );
    v___x_1703_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__44,
    );
    v___x_1704_ = lean_array_push(v___x_1703_, v___x_1702_);
    return v___x_1704_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47()
-> *mut leanh::LeanObject {
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1705_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__46,
    );
    v___x_1706_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
    v___x_1707_ = leanh::lean_box(2);
    v___x_1708_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1708_, 0, v___x_1707_);
    leanh::lean_ctor_set(v___x_1708_, 1, v___x_1706_);
    leanh::lean_ctor_set(v___x_1708_, 2, v___x_1705_);
    return v___x_1708_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48()
-> *mut leanh::LeanObject {
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1709_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__47,
    );
    v___x_1710_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31,
    );
    v___x_1711_ = lean_array_push(v___x_1710_, v___x_1709_);
    return v___x_1711_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49()
-> *mut leanh::LeanObject {
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1712_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5;
    v___x_1713_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__48,
    );
    v___x_1714_ = lean_array_push(v___x_1713_, v___x_1712_);
    return v___x_1714_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50()
-> *mut leanh::LeanObject {
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1715_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__49,
    );
    v___x_1716_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18;
    v___x_1717_ = leanh::lean_box(2);
    v___x_1718_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1718_, 0, v___x_1717_);
    leanh::lean_ctor_set(v___x_1718_, 1, v___x_1716_);
    leanh::lean_ctor_set(v___x_1718_, 2, v___x_1715_);
    return v___x_1718_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51()
-> *mut leanh::LeanObject {
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1719_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__50,
    );
    v___x_1720_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1721_ = lean_array_push(v___x_1720_, v___x_1719_);
    return v___x_1721_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53()
-> *mut leanh::LeanObject {
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1723_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__52;
    v___x_1724_ = l_Lean_mkAtom(v___x_1723_);
    return v___x_1724_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54()
-> *mut leanh::LeanObject {
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1725_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__53,
    );
    v___x_1726_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__51,
    );
    v___x_1727_ = lean_array_push(v___x_1726_, v___x_1725_);
    return v___x_1727_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57()
-> *mut leanh::LeanObject {
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1734_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__55;
    v___x_1735_ = l_Lean_mkAtom(v___x_1734_);
    return v___x_1735_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58()
-> *mut leanh::LeanObject {
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1736_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__57,
    );
    v___x_1737_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1738_ = lean_array_push(v___x_1737_, v___x_1736_);
    return v___x_1738_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59()
-> *mut leanh::LeanObject {
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1739_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5;
    v___x_1740_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__58,
    );
    v___x_1741_ = lean_array_push(v___x_1740_, v___x_1739_);
    return v___x_1741_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60()
-> *mut leanh::LeanObject {
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1742_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__59,
    );
    v___x_1743_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__56;
    v___x_1744_ = leanh::lean_box(2);
    v___x_1745_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1745_, 0, v___x_1744_);
    leanh::lean_ctor_set(v___x_1745_, 1, v___x_1743_);
    leanh::lean_ctor_set(v___x_1745_, 2, v___x_1742_);
    return v___x_1745_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61()
-> *mut leanh::LeanObject {
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1746_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__60,
    );
    v___x_1747_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__54,
    );
    v___x_1748_ = lean_array_push(v___x_1747_, v___x_1746_);
    return v___x_1748_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62()
-> *mut leanh::LeanObject {
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1749_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__61,
    );
    v___x_1750_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__16;
    v___x_1751_ = leanh::lean_box(2);
    v___x_1752_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1752_, 0, v___x_1751_);
    leanh::lean_ctor_set(v___x_1752_, 1, v___x_1750_);
    leanh::lean_ctor_set(v___x_1752_, 2, v___x_1749_);
    return v___x_1752_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63()
-> *mut leanh::LeanObject {
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1753_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__62,
    );
    v___x_1754_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1755_ = lean_array_push(v___x_1754_, v___x_1753_);
    return v___x_1755_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64()
-> *mut leanh::LeanObject {
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1756_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__63,
    );
    v___x_1757_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
    v___x_1758_ = leanh::lean_box(2);
    v___x_1759_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1759_, 0, v___x_1758_);
    leanh::lean_ctor_set(v___x_1759_, 1, v___x_1757_);
    leanh::lean_ctor_set(v___x_1759_, 2, v___x_1756_);
    return v___x_1759_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65()
-> *mut leanh::LeanObject {
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1760_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__64,
    );
    v___x_1761_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1762_ = lean_array_push(v___x_1761_, v___x_1760_);
    return v___x_1762_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66()
-> *mut leanh::LeanObject {
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1763_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__65,
    );
    v___x_1764_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32;
    v___x_1765_ = leanh::lean_box(2);
    v___x_1766_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1766_, 0, v___x_1765_);
    leanh::lean_ctor_set(v___x_1766_, 1, v___x_1764_);
    leanh::lean_ctor_set(v___x_1766_, 2, v___x_1763_);
    return v___x_1766_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67()
-> *mut leanh::LeanObject {
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1767_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__66,
    );
    v___x_1768_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1769_ = lean_array_push(v___x_1768_, v___x_1767_);
    return v___x_1769_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68()
-> *mut leanh::LeanObject {
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1770_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__67,
    );
    v___x_1771_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30;
    v___x_1772_ = leanh::lean_box(2);
    v___x_1773_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1773_, 0, v___x_1772_);
    leanh::lean_ctor_set(v___x_1773_, 1, v___x_1771_);
    leanh::lean_ctor_set(v___x_1773_, 2, v___x_1770_);
    return v___x_1773_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69()
-> *mut leanh::LeanObject {
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1774_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__68,
    );
    v___x_1775_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__14,
    );
    v___x_1776_ = lean_array_push(v___x_1775_, v___x_1774_);
    return v___x_1776_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70()
-> *mut leanh::LeanObject {
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__69,
    );
    v___x_1778_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__11;
    v___x_1779_ = leanh::lean_box(2);
    v___x_1780_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1780_, 0, v___x_1779_);
    leanh::lean_ctor_set(v___x_1780_, 1, v___x_1778_);
    leanh::lean_ctor_set(v___x_1780_, 2, v___x_1777_);
    return v___x_1780_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71()
-> *mut leanh::LeanObject {
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1781_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__70,
    );
    v___x_1782_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9,
    );
    v___x_1783_ = lean_array_push(v___x_1782_, v___x_1781_);
    return v___x_1783_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72()
-> *mut leanh::LeanObject {
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1784_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__71,
    );
    v___x_1785_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
    v___x_1786_ = leanh::lean_box(2);
    v___x_1787_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1787_, 0, v___x_1786_);
    leanh::lean_ctor_set(v___x_1787_, 1, v___x_1785_);
    leanh::lean_ctor_set(v___x_1787_, 2, v___x_1784_);
    return v___x_1787_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73()
-> *mut leanh::LeanObject {
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1788_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__72,
    );
    v___x_1789_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1790_ = lean_array_push(v___x_1789_, v___x_1788_);
    return v___x_1790_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74()
-> *mut leanh::LeanObject {
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1791_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__73,
    );
    v___x_1792_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32;
    v___x_1793_ = leanh::lean_box(2);
    v___x_1794_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1794_, 0, v___x_1793_);
    leanh::lean_ctor_set(v___x_1794_, 1, v___x_1792_);
    leanh::lean_ctor_set(v___x_1794_, 2, v___x_1791_);
    return v___x_1794_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75()
-> *mut leanh::LeanObject {
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1795_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__74,
    );
    v___x_1796_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1797_ = lean_array_push(v___x_1796_, v___x_1795_);
    return v___x_1797_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76()
-> *mut leanh::LeanObject {
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1798_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__75,
    );
    v___x_1799_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30;
    v___x_1800_ = leanh::lean_box(2);
    v___x_1801_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1801_, 0, v___x_1800_);
    leanh::lean_ctor_set(v___x_1801_, 1, v___x_1799_);
    leanh::lean_ctor_set(v___x_1801_, 2, v___x_1798_);
    return v___x_1801_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x3f__def___autoParam() -> *mut leanh::LeanObject
{
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1802_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__76,
    );
    return v___x_1802_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1803_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0;
    v___x_1804_ = lean_string_utf8_byte_size(v___x_1803_);
    return v___x_1804_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1805_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__0),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__0_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__0,
    );
    v___x_1806_ = leanh::lean_unsigned_to_nat(0);
    v___x_1807_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__0;
    v___x_1808_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1808_, 0, v___x_1807_);
    leanh::lean_ctor_set(v___x_1808_, 1, v___x_1806_);
    leanh::lean_ctor_set(v___x_1808_, 2, v___x_1805_);
    return v___x_1808_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1809_ = leanh::lean_box(0);
    v___x_1810_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d___x21__1___closed__2;
    v___x_1811_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__1),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__1_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__1,
    );
    v___x_1812_ = leanh::lean_box(2);
    v___x_1813_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1813_, 0, v___x_1812_);
    leanh::lean_ctor_set(v___x_1813_, 1, v___x_1811_);
    leanh::lean_ctor_set(v___x_1813_, 2, v___x_1810_);
    leanh::lean_ctor_set(v___x_1813_, 3, v___x_1809_);
    return v___x_1813_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1814_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__2),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__2_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__2,
    );
    v___x_1815_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36,
    );
    v___x_1816_ = lean_array_push(v___x_1815_, v___x_1814_);
    return v___x_1816_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1817_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__3),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__3_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__3,
    );
    v___x_1818_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35;
    v___x_1819_ = leanh::lean_box(2);
    v___x_1820_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1820_, 0, v___x_1819_);
    leanh::lean_ctor_set(v___x_1820_, 1, v___x_1818_);
    leanh::lean_ctor_set(v___x_1820_, 2, v___x_1817_);
    return v___x_1820_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1821_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__4),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__4_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__4,
    );
    v___x_1822_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1823_ = lean_array_push(v___x_1822_, v___x_1821_);
    return v___x_1823_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1825_ = l_LawfulGetElem_getElem_x21__def___autoParam___closed__6;
    v___x_1826_ = l_Lean_mkAtom(v___x_1825_);
    return v___x_1826_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1827_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__7),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__7_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__7,
    );
    v___x_1828_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__5),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__5_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__5,
    );
    v___x_1829_ = lean_array_push(v___x_1828_, v___x_1827_);
    return v___x_1829_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1830_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__41,
    );
    v___x_1831_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__8),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__8_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__8,
    );
    v___x_1832_ = lean_array_push(v___x_1831_, v___x_1830_);
    return v___x_1832_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1833_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__7),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__7_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__7,
    );
    v___x_1834_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__9),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__9_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__9,
    );
    v___x_1835_ = lean_array_push(v___x_1834_, v___x_1833_);
    return v___x_1835_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1837_ = l_LawfulGetElem_getElem_x21__def___autoParam___closed__11;
    v___x_1838_ = lean_string_utf8_byte_size(v___x_1837_);
    return v___x_1838_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1839_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__12),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__12_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__12,
    );
    v___x_1840_ = leanh::lean_unsigned_to_nat(0);
    v___x_1841_ = l_LawfulGetElem_getElem_x21__def___autoParam___closed__11;
    v___x_1842_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1842_, 0, v___x_1841_);
    leanh::lean_ctor_set(v___x_1842_, 1, v___x_1840_);
    leanh::lean_ctor_set(v___x_1842_, 2, v___x_1839_);
    return v___x_1842_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1845_ = leanh::lean_box(0);
    v___x_1846_ = l_LawfulGetElem_getElem_x21__def___autoParam___closed__14;
    v___x_1847_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__13),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__13_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__13,
    );
    v___x_1848_ = leanh::lean_box(2);
    v___x_1849_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1849_, 0, v___x_1848_);
    leanh::lean_ctor_set(v___x_1849_, 1, v___x_1847_);
    leanh::lean_ctor_set(v___x_1849_, 2, v___x_1846_);
    leanh::lean_ctor_set(v___x_1849_, 3, v___x_1845_);
    return v___x_1849_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1850_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__15),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__15_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__15,
    );
    v___x_1851_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__36,
    );
    v___x_1852_ = lean_array_push(v___x_1851_, v___x_1850_);
    return v___x_1852_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1853_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__16),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__16_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__16,
    );
    v___x_1854_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__35;
    v___x_1855_ = leanh::lean_box(2);
    v___x_1856_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1856_, 0, v___x_1855_);
    leanh::lean_ctor_set(v___x_1856_, 1, v___x_1854_);
    leanh::lean_ctor_set(v___x_1856_, 2, v___x_1853_);
    return v___x_1856_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1857_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__17),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__17_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__17,
    );
    v___x_1858_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__10),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__10_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__10,
    );
    v___x_1859_ = lean_array_push(v___x_1858_, v___x_1857_);
    return v___x_1859_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1860_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__18),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__18_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__18,
    );
    v___x_1861_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
    v___x_1862_ = leanh::lean_box(2);
    v___x_1863_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1863_, 0, v___x_1862_);
    leanh::lean_ctor_set(v___x_1863_, 1, v___x_1861_);
    leanh::lean_ctor_set(v___x_1863_, 2, v___x_1860_);
    return v___x_1863_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1864_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__19),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__19_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__19,
    );
    v___x_1865_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__33,
    );
    v___x_1866_ = lean_array_push(v___x_1865_, v___x_1864_);
    return v___x_1866_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1867_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__45,
    );
    v___x_1868_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__20),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__20_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__20,
    );
    v___x_1869_ = lean_array_push(v___x_1868_, v___x_1867_);
    return v___x_1869_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1870_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__21),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__21_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__21,
    );
    v___x_1871_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
    v___x_1872_ = leanh::lean_box(2);
    v___x_1873_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1873_, 0, v___x_1872_);
    leanh::lean_ctor_set(v___x_1873_, 1, v___x_1871_);
    leanh::lean_ctor_set(v___x_1873_, 2, v___x_1870_);
    return v___x_1873_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1874_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__22),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__22_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__22,
    );
    v___x_1875_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__31,
    );
    v___x_1876_ = lean_array_push(v___x_1875_, v___x_1874_);
    return v___x_1876_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1877_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__5;
    v___x_1878_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__23),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__23_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__23,
    );
    v___x_1879_ = lean_array_push(v___x_1878_, v___x_1877_);
    return v___x_1879_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1880_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__24),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__24_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__24,
    );
    v___x_1881_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__18;
    v___x_1882_ = leanh::lean_box(2);
    v___x_1883_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1883_, 0, v___x_1882_);
    leanh::lean_ctor_set(v___x_1883_, 1, v___x_1881_);
    leanh::lean_ctor_set(v___x_1883_, 2, v___x_1880_);
    return v___x_1883_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1884_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__25),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__25_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__25,
    );
    v___x_1885_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9_once),
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam___closed__9,
    );
    v___x_1886_ = lean_array_push(v___x_1885_, v___x_1884_);
    return v___x_1886_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1887_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__26),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__26_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__26,
    );
    v___x_1888_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
    v___x_1889_ = leanh::lean_box(2);
    v___x_1890_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1890_, 0, v___x_1889_);
    leanh::lean_ctor_set(v___x_1890_, 1, v___x_1888_);
    leanh::lean_ctor_set(v___x_1890_, 2, v___x_1887_);
    return v___x_1890_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__28()
-> *mut leanh::LeanObject {
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1891_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__27),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__27_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__27,
    );
    v___x_1892_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1893_ = lean_array_push(v___x_1892_, v___x_1891_);
    return v___x_1893_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__29()
-> *mut leanh::LeanObject {
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1894_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__28),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__28_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__28,
    );
    v___x_1895_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32;
    v___x_1896_ = leanh::lean_box(2);
    v___x_1897_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1897_, 0, v___x_1896_);
    leanh::lean_ctor_set(v___x_1897_, 1, v___x_1895_);
    leanh::lean_ctor_set(v___x_1897_, 2, v___x_1894_);
    return v___x_1897_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__30()
-> *mut leanh::LeanObject {
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1898_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__29),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__29_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__29,
    );
    v___x_1899_ = l_LawfulGetElem_getElem_x3f__def___autoParam___closed__0;
    v___x_1900_ = lean_array_push(v___x_1899_, v___x_1898_);
    return v___x_1900_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__31()
-> *mut leanh::LeanObject {
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1901_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__30),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__30_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__30,
    );
    v___x_1902_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30;
    v___x_1903_ = leanh::lean_box(2);
    v___x_1904_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1904_, 0, v___x_1903_);
    leanh::lean_ctor_set(v___x_1904_, 1, v___x_1902_);
    leanh::lean_ctor_set(v___x_1904_, 2, v___x_1901_);
    return v___x_1904_;
}
pub unsafe fn _init_l_LawfulGetElem_getElem_x21__def___autoParam() -> *mut leanh::LeanObject
{
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1905_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__31),
        core::ptr::addr_of_mut!(l_LawfulGetElem_getElem_x21__def___autoParam___closed__31_once),
        _init_l_LawfulGetElem_getElem_x21__def___autoParam___closed__31,
    );
    return v___x_1905_;
}
pub unsafe fn l___private_Init_GetElem_0__GetElem_x3f_match__1_splitter___redArg(
    mut v_x_1906_: *mut leanh::LeanObject,
    mut v_h__1_1907_: *mut leanh::LeanObject,
    mut v_h__2_1908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1906_) == 0 {
        let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1907_);
        v___x_1909_ = leanh::lean_box(0);
        v___x_1910_ = leanh::lean_apply_1(v_h__2_1908_, v___x_1909_);
        return v___x_1910_;
    } else {
        let mut v_val_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1908_);
        v_val_1911_ = leanh::lean_ctor_get(v_x_1906_, 0);
        leanh::lean_inc(v_val_1911_);
        leanh::lean_dec_ref_known(v_x_1906_, 1);
        v___x_1912_ = leanh::lean_apply_1(v_h__1_1907_, v_val_1911_);
        return v___x_1912_;
    }
}
pub unsafe fn l___private_Init_GetElem_0__GetElem_x3f_match__1_splitter(
    mut v_elem_1913_: *mut leanh::LeanObject,
    mut v_motive_1914_: *mut leanh::LeanObject,
    mut v_x_1915_: *mut leanh::LeanObject,
    mut v_h__1_1916_: *mut leanh::LeanObject,
    mut v_h__2_1917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1915_) == 0 {
        let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1916_);
        v___x_1918_ = leanh::lean_box(0);
        v___x_1919_ = leanh::lean_apply_1(v_h__2_1917_, v___x_1918_);
        return v___x_1919_;
    } else {
        let mut v_val_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1917_);
        v_val_1920_ = leanh::lean_ctor_get(v_x_1915_, 0);
        leanh::lean_inc(v_val_1920_);
        leanh::lean_dec_ref_known(v_x_1915_, 1);
        v___x_1921_ = leanh::lean_apply_1(v_h__1_1916_, v_val_1920_);
        return v___x_1921_;
    }
}
pub unsafe fn l_Fin_instGetElemFinVal___redArg___lam__0(
    mut v_inst_1922_: *mut leanh::LeanObject,
    mut v_xs_1923_: *mut leanh::LeanObject,
    mut v_i_1924_: *mut leanh::LeanObject,
    mut v_h_1925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1926_ = leanh::lean_apply_3(
        v_inst_1922_,
        v_xs_1923_,
        v_i_1924_,
        leanh::lean_box(0),
    );
    return v___x_1926_;
}
pub unsafe fn l_Fin_instGetElemFinVal___redArg(
    mut v_inst_1927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1928_ = leanh::lean_alloc_closure(
        l_Fin_instGetElemFinVal___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1928_, 0, v_inst_1927_);
    return v___f_1928_;
}
pub unsafe fn l_Fin_instGetElemFinVal(
    mut v_cont_1929_: *mut leanh::LeanObject,
    mut v_elem_1930_: *mut leanh::LeanObject,
    mut v_dom_1931_: *mut leanh::LeanObject,
    mut v_n_1932_: *mut leanh::LeanObject,
    mut v_inst_1933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1934_ = leanh::lean_alloc_closure(
        l_Fin_instGetElemFinVal___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1934_, 0, v_inst_1933_);
    return v___f_1934_;
}
pub unsafe fn l_Fin_instGetElemFinVal___boxed(
    mut v_cont_1935_: *mut leanh::LeanObject,
    mut v_elem_1936_: *mut leanh::LeanObject,
    mut v_dom_1937_: *mut leanh::LeanObject,
    mut v_n_1938_: *mut leanh::LeanObject,
    mut v_inst_1939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1940_ = l_Fin_instGetElemFinVal(
        v_cont_1935_,
        v_elem_1936_,
        v_dom_1937_,
        v_n_1938_,
        v_inst_1939_,
    );
    leanh::lean_dec(v_n_1938_);
    return v_res_1940_;
}
pub unsafe fn l_Fin_instGetElem_x3fFinVal___redArg___lam__0(
    mut v_getElem_x3f_1941_: *mut leanh::LeanObject,
    mut v_xs_1942_: *mut leanh::LeanObject,
    mut v_i_1943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1944_ = leanh::lean_apply_2(v_getElem_x3f_1941_, v_xs_1942_, v_i_1943_);
    return v___x_1944_;
}
pub unsafe fn l_Fin_instGetElem_x3fFinVal___redArg___lam__1(
    mut v_getElem_x21_1945_: *mut leanh::LeanObject,
    mut v_inst_1946_: *mut leanh::LeanObject,
    mut v_xs_1947_: *mut leanh::LeanObject,
    mut v_i_1948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1949_ =
        leanh::lean_apply_3(v_getElem_x21_1945_, v_inst_1946_, v_xs_1947_, v_i_1948_);
    return v___x_1949_;
}
pub unsafe fn l_Fin_instGetElem_x3fFinVal___redArg(
    mut v_inst_1950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toGetElem_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getElem_x3f_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getElem_x21_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1956_: u8 = 0;
    let mut v___f_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1963_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toGetElem_1951_ = leanh::lean_ctor_get(v_inst_1950_, 0);
                v_getElem_x3f_1952_ = leanh::lean_ctor_get(v_inst_1950_, 1);
                v_getElem_x21_1953_ = leanh::lean_ctor_get(v_inst_1950_, 2);
                v_isSharedCheck_1963_ = (!leanh::lean_is_exclusive(v_inst_1950_)) as u8;
                if v_isSharedCheck_1963_ == 0 {
                    v___x_1955_ = v_inst_1950_;
                    v_isShared_1956_ = v_isSharedCheck_1963_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_getElem_x21_1953_);
                    leanh::lean_inc(v_getElem_x3f_1952_);
                    leanh::lean_inc(v_toGetElem_1951_);
                    leanh::lean_dec(v_inst_1950_);
                    v___x_1955_ = leanh::lean_box(0);
                    v_isShared_1956_ = v_isSharedCheck_1963_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1957_ = leanh::lean_alloc_closure(
                    l_Fin_instGetElem_x3fFinVal___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    1,
                );
                leanh::lean_closure_set(v___f_1957_, 0, v_getElem_x3f_1952_);
                v___f_1958_ = leanh::lean_alloc_closure(
                    l_Fin_instGetElem_x3fFinVal___redArg___lam__1 as *mut core::ffi::c_void,
                    4,
                    1,
                );
                leanh::lean_closure_set(v___f_1958_, 0, v_getElem_x21_1953_);
                v___f_1959_ = leanh::lean_alloc_closure(
                    l_Fin_instGetElemFinVal___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    1,
                );
                leanh::lean_closure_set(v___f_1959_, 0, v_toGetElem_1951_);
                if v_isShared_1956_ == 0 {
                    leanh::lean_ctor_set(v___x_1955_, 2, v___f_1958_);
                    leanh::lean_ctor_set(v___x_1955_, 1, v___f_1957_);
                    leanh::lean_ctor_set(v___x_1955_, 0, v___f_1959_);
                    v___x_1961_ = v___x_1955_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1962_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___f_1959_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 1, v___f_1957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 2, v___f_1958_);
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
    mut v_cont_1964_: *mut leanh::LeanObject,
    mut v_elem_1965_: *mut leanh::LeanObject,
    mut v_dom_1966_: *mut leanh::LeanObject,
    mut v_n_1967_: *mut leanh::LeanObject,
    mut v_inst_1968_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1969_ = l_Fin_instGetElem_x3fFinVal___redArg(v_inst_1968_);
    return v___x_1969_;
}
pub unsafe fn l_Fin_instGetElem_x3fFinVal___boxed(
    mut v_cont_1970_: *mut leanh::LeanObject,
    mut v_elem_1971_: *mut leanh::LeanObject,
    mut v_dom_1972_: *mut leanh::LeanObject,
    mut v_n_1973_: *mut leanh::LeanObject,
    mut v_inst_1974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1975_ = l_Fin_instGetElem_x3fFinVal(
        v_cont_1970_,
        v_elem_1971_,
        v_dom_1972_,
        v_n_1973_,
        v_inst_1974_,
    );
    leanh::lean_dec(v_n_1973_);
    return v_res_1975_;
}
pub unsafe fn _init_l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2004_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__10;
    v___x_2005_ = l_String_toRawSubstring_x27(v___x_2004_);
    return v___x_2005_;
}
pub unsafe fn l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1(
    mut v_x_2025_: *mut leanh::LeanObject,
    mut v_a_2026_: *mut leanh::LeanObject,
    mut v_a_2027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: u8 = 0;
    v___x_2028_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__1;
    v___x_2029_ = l_Lean_Syntax_isOfKind(v_x_2025_, v___x_2028_);
    if v___x_2029_ == 0 {
        let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2030_ = leanh::lean_box(1);
        v___x_2031_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2031_, 0, v___x_2030_);
        leanh::lean_ctor_set(v___x_2031_, 1, v_a_2027_);
        return v___x_2031_;
    } else {
        let mut v_quotContext_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2035_: u8 = 0;
        let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2032_ = leanh::lean_ctor_get(v_a_2026_, 1);
        v_currMacroScope_2033_ = leanh::lean_ctor_get(v_a_2026_, 2);
        v_ref_2034_ = leanh::lean_ctor_get(v_a_2026_, 5);
        v___x_2035_ = 0;
        v___x_2036_ = l_Lean_SourceInfo_fromRef(v_ref_2034_, v___x_2035_);
        v___x_2037_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__3;
        v___x_2038_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__13;
        v___x_2039_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__4;
        v___x_2040_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__18;
        leanh::lean_inc_n(v___x_2036_, 20);
        v___x_2041_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2041_, 0, v___x_2036_);
        leanh::lean_ctor_set(v___x_2041_, 1, v___x_2040_);
        v___x_2042_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__30;
        v___x_2043_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__32;
        v___x_2044_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__6;
        v___x_2045_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__7;
        v___x_2046_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2046_, 0, v___x_2036_);
        leanh::lean_ctor_set(v___x_2046_, 1, v___x_2045_);
        v___x_2047_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__8;
        v___x_2048_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__9;
        v___x_2049_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2049_, 0, v___x_2036_);
        leanh::lean_ctor_set(v___x_2049_, 1, v___x_2047_);
        v___x_2050_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11), core::ptr::addr_of_mut!(l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_once), _init_l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__11);
        v___x_2051_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__14;
        leanh::lean_inc(v_currMacroScope_2033_);
        leanh::lean_inc(v_quotContext_2032_);
        v___x_2052_ =
            l_Lean_addMacroScope(v_quotContext_2032_, v___x_2051_, v_currMacroScope_2033_);
        v___x_2053_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__16;
        v___x_2054_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2054_, 0, v___x_2036_);
        leanh::lean_ctor_set(v___x_2054_, 1, v___x_2050_);
        leanh::lean_ctor_set(v___x_2054_, 2, v___x_2052_);
        leanh::lean_ctor_set(v___x_2054_, 3, v___x_2053_);
        v___x_2055_ = l_Lean_Syntax_node2(v___x_2036_, v___x_2048_, v___x_2049_, v___x_2054_);
        v___x_2056_ = l_Lean_Syntax_node1(v___x_2036_, v___x_2038_, v___x_2055_);
        v___x_2057_ = l_Lean_Syntax_node1(v___x_2036_, v___x_2043_, v___x_2056_);
        v___x_2058_ = l_Lean_Syntax_node1(v___x_2036_, v___x_2042_, v___x_2057_);
        v___x_2059_ = l_Lean_Syntax_node2(v___x_2036_, v___x_2044_, v___x_2046_, v___x_2058_);
        v___x_2060_ = l_Lean_Syntax_node1(v___x_2036_, v___x_2038_, v___x_2059_);
        v___x_2061_ = l_Lean_Syntax_node1(v___x_2036_, v___x_2043_, v___x_2060_);
        v___x_2062_ = l_Lean_Syntax_node1(v___x_2036_, v___x_2042_, v___x_2061_);
        v___x_2063_ = l___aux__Init__GetElem______macroRules__term_____x5b___x5d__1___closed__36;
        v___x_2064_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2064_, 0, v___x_2036_);
        leanh::lean_ctor_set(v___x_2064_, 1, v___x_2063_);
        v___x_2065_ = l_Lean_Syntax_node3(
            v___x_2036_,
            v___x_2039_,
            v___x_2041_,
            v___x_2062_,
            v___x_2064_,
        );
        v___x_2066_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__17;
        v___x_2067_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2067_, 0, v___x_2036_);
        leanh::lean_ctor_set(v___x_2067_, 1, v___x_2066_);
        v___x_2068_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__18;
        v___x_2069_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2069_, 0, v___x_2036_);
        leanh::lean_ctor_set(v___x_2069_, 1, v___x_2068_);
        v___x_2070_ = l_Lean_Syntax_node1(v___x_2036_, v___x_2028_, v___x_2069_);
        v___x_2071_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__19;
        v___x_2072_ = l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___closed__20;
        v___x_2073_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2073_, 0, v___x_2036_);
        leanh::lean_ctor_set(v___x_2073_, 1, v___x_2071_);
        v___x_2074_ = l_Lean_Syntax_node1(v___x_2036_, v___x_2072_, v___x_2073_);
        leanh::lean_inc_ref(v___x_2067_);
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
        v___x_2077_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2077_, 0, v___x_2076_);
        leanh::lean_ctor_set(v___x_2077_, 1, v_a_2027_);
        return v___x_2077_;
    }
}
pub unsafe fn l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1___boxed(
    mut v_x_2078_: *mut leanh::LeanObject,
    mut v_a_2079_: *mut leanh::LeanObject,
    mut v_a_2080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2081_ =
        l_Fin___aux__Init__GetElem______macroRules__tacticGet__elem__tactic__extensible__1(
            v_x_2078_, v_a_2079_, v_a_2080_,
        );
    leanh::lean_dec_ref(v_a_2079_);
    return v_res_2081_;
}
pub unsafe fn l_List_instGetElemNatLtLength___lam__0(
    mut v_as_2082_: *mut leanh::LeanObject,
    mut v_i_2083_: *mut leanh::LeanObject,
    mut v_h_2084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2085_ = l_List_get___redArg(v_as_2082_, v_i_2083_);
    return v___x_2085_;
}
pub unsafe fn l_List_instGetElemNatLtLength___lam__0___boxed(
    mut v_as_2086_: *mut leanh::LeanObject,
    mut v_i_2087_: *mut leanh::LeanObject,
    mut v_h_2088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2089_ = l_List_instGetElemNatLtLength___lam__0(v_as_2086_, v_i_2087_, v_h_2088_);
    leanh::lean_dec(v_as_2086_);
    return v_res_2089_;
}
pub unsafe fn l_List_instGetElemNatLtLength(
    mut v_00_u03b1_2091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2092_ = l_List_instGetElemNatLtLength___closed__0;
    return v___f_2092_;
}
pub unsafe fn l_List_get_x3fInternal___redArg(
    mut v_x_2093_: *mut leanh::LeanObject,
    mut v_x_2094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2098_: u8 = 0;
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2093_) == 1 {
                    v_head_2095_ = leanh::lean_ctor_get(v_x_2093_, 0);
                    v_tail_2096_ = leanh::lean_ctor_get(v_x_2093_, 1);
                    v_zero_2097_ = leanh::lean_unsigned_to_nat(0);
                    v_isZero_2098_ = lean_nat_dec_eq(v_x_2094_, v_zero_2097_);
                    if v_isZero_2098_ == 1 {
                        leanh::lean_dec(v_x_2094_);
                        leanh::lean_inc(v_head_2095_);
                        v___x_2099_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2099_, 0, v_head_2095_);
                        return v___x_2099_;
                    } else {
                        v_one_2100_ = leanh::lean_unsigned_to_nat(1);
                        v_n_2101_ = lean_nat_sub(v_x_2094_, v_one_2100_);
                        leanh::lean_dec(v_x_2094_);
                        v_x_2093_ = v_tail_2096_;
                        v_x_2094_ = v_n_2101_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_x_2094_);
                    v___x_2103_ = leanh::lean_box(0);
                    return v___x_2103_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_get_x3fInternal___redArg___boxed(
    mut v_x_2104_: *mut leanh::LeanObject,
    mut v_x_2105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2106_ = l_List_get_x3fInternal___redArg(v_x_2104_, v_x_2105_);
    leanh::lean_dec(v_x_2104_);
    return v_res_2106_;
}
pub unsafe fn l_List_get_x3fInternal(
    mut v_00_u03b1_2107_: *mut leanh::LeanObject,
    mut v_x_2108_: *mut leanh::LeanObject,
    mut v_x_2109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2110_ = l_List_get_x3fInternal___redArg(v_x_2108_, v_x_2109_);
    return v___x_2110_;
}
pub unsafe fn l_List_get_x3fInternal___boxed(
    mut v_00_u03b1_2111_: *mut leanh::LeanObject,
    mut v_x_2112_: *mut leanh::LeanObject,
    mut v_x_2113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2114_ = l_List_get_x3fInternal(v_00_u03b1_2111_, v_x_2112_, v_x_2113_);
    leanh::lean_dec(v_x_2112_);
    return v_res_2114_;
}
pub unsafe fn l_List_get_x21Internal___redArg(
    mut v_inst_2117_: *mut leanh::LeanObject,
    mut v_x_2118_: *mut leanh::LeanObject,
    mut v_x_2119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2123_: u8 = 0;
    let mut v_one_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2118_) == 1 {
                    v_head_2120_ = leanh::lean_ctor_get(v_x_2118_, 0);
                    v_tail_2121_ = leanh::lean_ctor_get(v_x_2118_, 1);
                    v_zero_2122_ = leanh::lean_unsigned_to_nat(0);
                    v_isZero_2123_ = lean_nat_dec_eq(v_x_2119_, v_zero_2122_);
                    if v_isZero_2123_ == 1 {
                        leanh::lean_dec(v_x_2119_);
                        leanh::lean_inc(v_head_2120_);
                        return v_head_2120_;
                    } else {
                        v_one_2124_ = leanh::lean_unsigned_to_nat(1);
                        v_n_2125_ = lean_nat_sub(v_x_2119_, v_one_2124_);
                        leanh::lean_dec(v_x_2119_);
                        v_x_2118_ = v_tail_2121_;
                        v_x_2119_ = v_n_2125_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_x_2119_);
                    v___x_2127_ = l_outOfBounds___redArg___closed__0;
                    v___x_2128_ = l_List_get_x21Internal___redArg___closed__0;
                    v___x_2129_ = leanh::lean_unsigned_to_nat(332);
                    v___x_2130_ = leanh::lean_unsigned_to_nat(18);
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
    mut v_inst_2134_: *mut leanh::LeanObject,
    mut v_x_2135_: *mut leanh::LeanObject,
    mut v_x_2136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2137_ = l_List_get_x21Internal___redArg(v_inst_2134_, v_x_2135_, v_x_2136_);
    leanh::lean_dec(v_x_2135_);
    leanh::lean_dec(v_inst_2134_);
    return v_res_2137_;
}
pub unsafe fn l_List_get_x21Internal(
    mut v_00_u03b1_2138_: *mut leanh::LeanObject,
    mut v_inst_2139_: *mut leanh::LeanObject,
    mut v_x_2140_: *mut leanh::LeanObject,
    mut v_x_2141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2142_ = l_List_get_x21Internal___redArg(v_inst_2139_, v_x_2140_, v_x_2141_);
    return v___x_2142_;
}
pub unsafe fn l_List_get_x21Internal___boxed(
    mut v_00_u03b1_2143_: *mut leanh::LeanObject,
    mut v_inst_2144_: *mut leanh::LeanObject,
    mut v_x_2145_: *mut leanh::LeanObject,
    mut v_x_2146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2147_ = l_List_get_x21Internal(v_00_u03b1_2143_, v_inst_2144_, v_x_2145_, v_x_2146_);
    leanh::lean_dec(v_x_2145_);
    leanh::lean_dec(v_inst_2144_);
    return v_res_2147_;
}
pub unsafe fn l_List_instGetElem_x3fNatLtLength(
    mut v_00_u03b1_2154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2155_ = l_List_instGetElem_x3fNatLtLength___closed__2;
    return v___x_2155_;
}
pub unsafe fn l_Array_instGetElemNatLtSize___lam__0(
    mut v_xs_2156_: *mut leanh::LeanObject,
    mut v_i_2157_: *mut leanh::LeanObject,
    mut v_h_2158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2159_ = lean_array_fget_borrowed(v_xs_2156_, v_i_2157_);
    leanh::lean_inc(v___x_2159_);
    return v___x_2159_;
}
pub unsafe fn l_Array_instGetElemNatLtSize___lam__0___boxed(
    mut v_xs_2160_: *mut leanh::LeanObject,
    mut v_i_2161_: *mut leanh::LeanObject,
    mut v_h_2162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2163_ = l_Array_instGetElemNatLtSize___lam__0(v_xs_2160_, v_i_2161_, v_h_2162_);
    leanh::lean_dec(v_i_2161_);
    leanh::lean_dec_ref(v_xs_2160_);
    return v_res_2163_;
}
pub unsafe fn l_Array_instGetElemNatLtSize(
    mut v_00_u03b1_2165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2166_ = l_Array_instGetElemNatLtSize___closed__0;
    return v___f_2166_;
}
pub unsafe fn l_Array_instGetElem_x3fNatLtSize___lam__0(
    mut v_xs_2167_: *mut leanh::LeanObject,
    mut v_i_2168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: u8 = 0;
    v___x_2169_ = lean_array_get_size(v_xs_2167_);
    v___x_2170_ = lean_nat_dec_lt(v_i_2168_, v___x_2169_);
    if v___x_2170_ == 0 {
        let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2171_ = leanh::lean_box(0);
        return v___x_2171_;
    } else {
        let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2172_ = lean_array_fget_borrowed(v_xs_2167_, v_i_2168_);
        leanh::lean_inc(v___x_2172_);
        v___x_2173_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2173_, 0, v___x_2172_);
        return v___x_2173_;
    }
}
pub unsafe fn l_Array_instGetElem_x3fNatLtSize___lam__0___boxed(
    mut v_xs_2174_: *mut leanh::LeanObject,
    mut v_i_2175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2176_ = l_Array_instGetElem_x3fNatLtSize___lam__0(v_xs_2174_, v_i_2175_);
    leanh::lean_dec(v_i_2175_);
    leanh::lean_dec_ref(v_xs_2174_);
    return v_res_2176_;
}
pub unsafe fn l_Array_instGetElem_x3fNatLtSize___lam__1(
    mut v_inst_2177_: *mut leanh::LeanObject,
    mut v_xs_2178_: *mut leanh::LeanObject,
    mut v_i_2179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2180_ = lean_array_get_borrowed(v_inst_2177_, v_xs_2178_, v_i_2179_);
    leanh::lean_inc(v___x_2180_);
    return v___x_2180_;
}
pub unsafe fn l_Array_instGetElem_x3fNatLtSize___lam__1___boxed(
    mut v_inst_2181_: *mut leanh::LeanObject,
    mut v_xs_2182_: *mut leanh::LeanObject,
    mut v_i_2183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2184_ = l_Array_instGetElem_x3fNatLtSize___lam__1(v_inst_2181_, v_xs_2182_, v_i_2183_);
    leanh::lean_dec(v_i_2183_);
    leanh::lean_dec_ref(v_xs_2182_);
    leanh::lean_dec(v_inst_2181_);
    return v_res_2184_;
}
pub unsafe fn l_Array_instGetElem_x3fNatLtSize(
    mut v_00_u03b1_2191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2192_ = l_Array_instGetElem_x3fNatLtSize___closed__2;
    return v___x_2192_;
}
pub unsafe fn l_Lean_Syntax_instGetElemNatTrue___lam__0(
    mut v_stx_2193_: *mut leanh::LeanObject,
    mut v_i_2194_: *mut leanh::LeanObject,
    mut v_x_2195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2196_ = l_Lean_Syntax_getArg(v_stx_2193_, v_i_2194_);
    return v___x_2196_;
}
pub unsafe fn l_Lean_Syntax_instGetElemNatTrue___lam__0___boxed(
    mut v_stx_2197_: *mut leanh::LeanObject,
    mut v_i_2198_: *mut leanh::LeanObject,
    mut v_x_2199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2200_ = l_Lean_Syntax_instGetElemNatTrue___lam__0(v_stx_2197_, v_i_2198_, v_x_2199_);
    leanh::lean_dec(v_i_2198_);
    leanh::lean_dec(v_stx_2197_);
    return v_res_2200_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_GetElem(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_GetElem(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_LawfulGetElem_getElem_x3f__def___autoParam =
        _init_l_LawfulGetElem_getElem_x3f__def___autoParam();
    leanh::lean_mark_persistent(l_LawfulGetElem_getElem_x3f__def___autoParam);
    l_LawfulGetElem_getElem_x21__def___autoParam =
        _init_l_LawfulGetElem_getElem_x21__def___autoParam();
    leanh::lean_mark_persistent(l_LawfulGetElem_getElem_x21__def___autoParam);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_GetElem(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_GetElem(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_GetElem(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_GetElem(builtin);
}