// Lean compiler output
// Module: Std.Do.SPred.Notation.Basic
// Imports: Std.Do.SPred.SPred
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesIdent, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_node5,
    l_Lean_Syntax_node6, l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::r#gen::Std::Do::SPred::SPred::{
    initialize_Std_Do_SPred_SPred, runtime_initialize_Std_Do_SPred_SPred,
};
pub static l_Std_Do_termSpred_x28___x29___closed__0_value: leanh::LeanStringObject<4> =
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
        m_data: [83, 116, 100, 0],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__1_value: leanh::LeanStringObject<3> =
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
        m_data: [68, 111, 0],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__2_value: leanh::LeanStringObject<13> =
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
        m_data: [116, 101, 114, 109, 83, 112, 114, 101, 100, 40, 95, 41, 0],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__2_value)
        as *mut leanh::LeanObject;
static l_Std_Do_termSpred_x28___x29___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
static l_Std_Do_termSpred_x28___x29___closed__3_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__1_value)
                as *mut leanh::LeanObject,
            7300584325018775040 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_Do_termSpred_x28___x29___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__3_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__2_value)
                as *mut leanh::LeanObject,
            13979102795498516556 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__4_value: leanh::LeanStringObject<8> =
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
static mut l_Std_Do_termSpred_x28___x29___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__4_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__6_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [115, 112, 114, 101, 100, 40, 0],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__7_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__8_value: leanh::LeanStringObject<5> =
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
static mut l_Std_Do_termSpred_x28___x29___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__8_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__10_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__9_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__11_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__12_value: leanh::LeanStringObject<2> =
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
        m_data: [41, 0],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__13_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__14_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__11_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__13_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__15_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__3_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__15_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Do_termSpred_x28___x29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termTerm_x28___x29___closed__0_value: leanh::LeanStringObject<12> =
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
        m_data: [116, 101, 114, 109, 84, 101, 114, 109, 40, 95, 41, 0],
    };
static mut l_Std_Do_termTerm_x28___x29___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_Do_termTerm_x28___x29___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
static l_Std_Do_termTerm_x28___x29___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__1_value)
                as *mut leanh::LeanObject,
            7300584325018775040 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_Do_termTerm_x28___x29___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__0_value)
                as *mut leanh::LeanObject,
            11926647143693398162 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termTerm_x28___x29___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termTerm_x28___x29___closed__2_value: leanh::LeanStringObject<6> =
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
        m_data: [116, 101, 114, 109, 40, 0],
    };
static mut l_Std_Do_termTerm_x28___x29___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termTerm_x28___x29___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termTerm_x28___x29___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termTerm_x28___x29___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termTerm_x28___x29___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termTerm_x28___x29___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__13_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termTerm_x28___x29___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_termTerm_x28___x29___closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termTerm_x28___x29___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__6_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Do_termTerm_x28___x29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__3_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__3_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__3_value) as *mut leanh::LeanObject,7932075773091973500 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__5_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [102, 117, 110, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__5_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__5_value) as *mut leanh::LeanObject,7043493786777132025 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__7_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 101, 114, 109, 73, 102, 84, 104, 101, 110, 69, 108, 115, 101, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__7_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__7_value) as *mut leanh::LeanObject,14296711813398647265 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__8_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__9_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 121, 112, 101, 65, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__9_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__9_value) as *mut leanh::LeanObject,5346268661279150583 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__11_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__11_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__11_value) as *mut leanh::LeanObject,7306243862518720553 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__13_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__13_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__13_value) as *mut leanh::LeanObject,9871775667037945883 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__16_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__16_value) as *mut leanh::LeanObject;
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__18_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__18_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__18_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__18_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__19_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__18_value) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__19_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__21_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__21_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__21_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20_value) as *mut leanh::LeanObject,300274991653824376 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__21_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__22_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__21_value) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__22_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__23_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__23_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__23_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__23_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__24_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__23_value) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__24_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [77, 97, 99, 114, 111, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__26_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__26_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__26_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25_value) as *mut leanh::LeanObject,18105168627502861736 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__26_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__27_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__26_value) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__27_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__28_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__28_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__29_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__28_value) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__29_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__30_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__29_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__30_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__31_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__27_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__30_value) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__31_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__32_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__24_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__31_value) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__32_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__33_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__22_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__32_value) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__33: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__33_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__34_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__19_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__33_value) as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__34: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__34_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__35_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__35: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__35_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__36_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__36: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__36_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__36_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__38_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 102, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__38: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__38_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__39_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 104, 101, 110, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__39: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__39_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__40_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [101, 108, 115, 101, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__40: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__40_value) as *mut leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__41_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 97, 115, 105, 99, 70, 117, 110, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__41: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__41_value) as *mut leanh::LeanObject;
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__41_value) as *mut leanh::LeanObject,16077784126176397009 as *mut leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value) as *mut leanh::LeanObject;
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__44_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__44: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__44_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__0_value:
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
    m_data: [83, 80, 114, 101, 100, 0],
};
static mut l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__1_value:
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
    m_data: [78, 111, 116, 97, 116, 105, 111, 110, 0],
};
static mut l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__1___redArg(
    mut v_x_1066_: *mut leanh::LeanObject,
    mut v_a_1067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: u8 = 0;
    v___x_1068_ = l_Std_Do_termSpred_x28___x29___closed__3;
    leanh::lean_inc(v_x_1066_);
    v___x_1069_ = l_Lean_Syntax_isOfKind(v_x_1066_, v___x_1068_);
    if v___x_1069_ == 0 {
        let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1066_);
        v___x_1070_ = leanh::lean_box(1);
        v___x_1071_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1071_, 0, v___x_1070_);
        leanh::lean_ctor_set(v___x_1071_, 1, v_a_1067_);
        return v___x_1071_;
    } else {
        let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1075_: u8 = 0;
        v___x_1072_ = leanh::lean_unsigned_to_nat(1);
        v___x_1073_ = l_Lean_Syntax_getArg(v_x_1066_, v___x_1072_);
        leanh::lean_dec(v_x_1066_);
        v___x_1074_ = l_Std_Do_termTerm_x28___x29___closed__1;
        leanh::lean_inc(v___x_1073_);
        v___x_1075_ = l_Lean_Syntax_isOfKind(v___x_1073_, v___x_1074_);
        if v___x_1075_ == 0 {
            let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1076_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1076_, 0, v___x_1073_);
            leanh::lean_ctor_set(v___x_1076_, 1, v_a_1067_);
            return v___x_1076_;
        } else {
            let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1077_ = l_Lean_Syntax_getArg(v___x_1073_, v___x_1072_);
            leanh::lean_dec(v___x_1073_);
            v___x_1078_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1078_, 0, v___x_1077_);
            leanh::lean_ctor_set(v___x_1078_, 1, v_a_1067_);
            return v___x_1078_;
        }
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__1(
    mut v_x_1079_: *mut leanh::LeanObject,
    mut v_a_1080_: *mut leanh::LeanObject,
    mut v_a_1081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1082_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__1___redArg(v_x_1079_, v_a_1081_);
    return v___x_1082_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__1___boxed(
    mut v_x_1083_: *mut leanh::LeanObject,
    mut v_a_1084_: *mut leanh::LeanObject,
    mut v_a_1085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1086_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__1(v_x_1083_, v_a_1084_, v_a_1085_);
    leanh::lean_dec_ref(v_a_1084_);
    return v_res_1086_;
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1122_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__16;
    v___x_1123_ = l_String_toRawSubstring_x27(v___x_1122_);
    return v___x_1123_;
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43()
-> *mut leanh::LeanObject {
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1178_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_1178_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2(
    mut v_x_1180_: *mut leanh::LeanObject,
    mut v_a_1181_: *mut leanh::LeanObject,
    mut v_a_1182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: u8 = 0;
    v___x_1183_ = l_Std_Do_termSpred_x28___x29___closed__3;
    leanh::lean_inc(v_x_1180_);
    v___x_1184_ = l_Lean_Syntax_isOfKind(v_x_1180_, v___x_1183_);
    if v___x_1184_ == 0 {
        let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1180_);
        v___x_1185_ = leanh::lean_box(1);
        v___x_1186_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1186_, 0, v___x_1185_);
        leanh::lean_ctor_set(v___x_1186_, 1, v_a_1182_);
        return v___x_1186_;
    } else {
        let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1191_: u8 = 0;
        v___x_1187_ = leanh::lean_unsigned_to_nat(0);
        v___x_1188_ = leanh::lean_unsigned_to_nat(1);
        v___x_1189_ = l_Lean_Syntax_getArg(v_x_1180_, v___x_1188_);
        leanh::lean_dec(v_x_1180_);
        v___x_1190_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4;
        leanh::lean_inc(v___x_1189_);
        v___x_1191_ = l_Lean_Syntax_isOfKind(v___x_1189_, v___x_1190_);
        if v___x_1191_ == 0 {
            let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1194_: u8 = 0;
            v___x_1192_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__5;
            v___x_1193_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6;
            leanh::lean_inc(v___x_1189_);
            v___x_1194_ = l_Lean_Syntax_isOfKind(v___x_1189_, v___x_1193_);
            if v___x_1194_ == 0 {
                let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1196_: u8 = 0;
                v___x_1195_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__8;
                leanh::lean_inc(v___x_1189_);
                v___x_1196_ = l_Lean_Syntax_isOfKind(v___x_1189_, v___x_1195_);
                if v___x_1196_ == 0 {
                    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1198_: u8 = 0;
                    v___x_1197_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10;
                    leanh::lean_inc(v___x_1189_);
                    v___x_1198_ = l_Lean_Syntax_isOfKind(v___x_1189_, v___x_1197_);
                    if v___x_1198_ == 0 {
                        let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
                        leanh::lean_dec(v___x_1189_);
                        v___x_1199_ = leanh::lean_box(1);
                        v___x_1200_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1200_, 0, v___x_1199_);
                        leanh::lean_ctor_set(v___x_1200_, 1, v_a_1182_);
                        return v___x_1200_;
                    } else {
                        let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1203_: u8 = 0;
                        v___x_1201_ = l_Lean_Syntax_getArg(v___x_1189_, v___x_1187_);
                        v___x_1202_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12;
                        leanh::lean_inc(v___x_1201_);
                        v___x_1203_ = l_Lean_Syntax_isOfKind(v___x_1201_, v___x_1202_);
                        if v___x_1203_ == 0 {
                            let mut v___x_1204_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1205_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            leanh::lean_dec(v___x_1201_);
                            leanh::lean_dec(v___x_1189_);
                            v___x_1204_ = leanh::lean_box(1);
                            v___x_1205_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1205_, 0, v___x_1204_);
                            leanh::lean_ctor_set(v___x_1205_, 1, v_a_1182_);
                            return v___x_1205_;
                        } else {
                            let mut v___x_1206_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1207_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1208_: u8 = 0;
                            v___x_1206_ = l_Lean_Syntax_getArg(v___x_1201_, v___x_1188_);
                            leanh::lean_dec(v___x_1201_);
                            v___x_1207_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14;
                            leanh::lean_inc(v___x_1206_);
                            v___x_1208_ = l_Lean_Syntax_isOfKind(v___x_1206_, v___x_1207_);
                            if v___x_1208_ == 0 {
                                let mut v___x_1209_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1210_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                leanh::lean_dec(v___x_1206_);
                                leanh::lean_dec(v___x_1189_);
                                v___x_1209_ = leanh::lean_box(1);
                                v___x_1210_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1210_, 0, v___x_1209_);
                                leanh::lean_ctor_set(v___x_1210_, 1, v_a_1182_);
                                return v___x_1210_;
                            } else {
                                let mut v___x_1211_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1212_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1213_: u8 = 0;
                                v___x_1211_ = l_Lean_Syntax_getArg(v___x_1206_, v___x_1187_);
                                leanh::lean_dec(v___x_1206_);
                                v___x_1212_ = leanh::lean_box(0);
                                v___x_1213_ = l_Lean_Syntax_matchesIdent(v___x_1211_, v___x_1212_);
                                leanh::lean_dec(v___x_1211_);
                                if v___x_1213_ == 0 {
                                    let mut v___x_1214_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1215_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    leanh::lean_dec(v___x_1189_);
                                    v___x_1214_ = leanh::lean_box(1);
                                    v___x_1215_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_1215_, 0, v___x_1214_);
                                    leanh::lean_ctor_set(v___x_1215_, 1, v_a_1182_);
                                    return v___x_1215_;
                                } else {
                                    let mut v___x_1216_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1217_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1218_: u8 = 0;
                                    v___x_1216_ = leanh::lean_unsigned_to_nat(3);
                                    v___x_1217_ = l_Lean_Syntax_getArg(v___x_1189_, v___x_1216_);
                                    leanh::lean_inc(v___x_1217_);
                                    v___x_1218_ =
                                        l_Lean_Syntax_matchesNull(v___x_1217_, v___x_1188_);
                                    if v___x_1218_ == 0 {
                                        let mut v___x_1219_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1220_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        leanh::lean_dec(v___x_1217_);
                                        leanh::lean_dec(v___x_1189_);
                                        v___x_1219_ = leanh::lean_box(1);
                                        v___x_1220_ =
                                            leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_1220_, 0, v___x_1219_);
                                        leanh::lean_ctor_set(v___x_1220_, 1, v_a_1182_);
                                        return v___x_1220_;
                                    } else {
                                        let mut v_quotContext_1221_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v_currMacroScope_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
                                        let mut v_ref_1223_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1224_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1225_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1226_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1227_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1228_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1229_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1230_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1231_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1232_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1233_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1234_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1235_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1236_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1237_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1238_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1239_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1240_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1241_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1242_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1243_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1244_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1245_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        v_quotContext_1221_ =
                                            leanh::lean_ctor_get(v_a_1181_, 1);
                                        v_currMacroScope_1222_ =
                                            leanh::lean_ctor_get(v_a_1181_, 2);
                                        v_ref_1223_ = leanh::lean_ctor_get(v_a_1181_, 5);
                                        v___x_1224_ =
                                            l_Lean_Syntax_getArg(v___x_1189_, v___x_1188_);
                                        leanh::lean_dec(v___x_1189_);
                                        v___x_1225_ =
                                            l_Lean_Syntax_getArg(v___x_1217_, v___x_1187_);
                                        leanh::lean_dec(v___x_1217_);
                                        v___x_1226_ =
                                            l_Lean_SourceInfo_fromRef(v_ref_1223_, v___x_1196_);
                                        v___x_1227_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15;
                                        leanh::lean_inc_n(v___x_1226_, 9);
                                        v___x_1228_ =
                                            leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_1228_, 0, v___x_1226_);
                                        leanh::lean_ctor_set(v___x_1228_, 1, v___x_1227_);
                                        v___x_1229_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17_once), _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17);
                                        leanh::lean_inc(v_currMacroScope_1222_);
                                        leanh::lean_inc(v_quotContext_1221_);
                                        v___x_1230_ = l_Lean_addMacroScope(
                                            v_quotContext_1221_,
                                            v___x_1212_,
                                            v_currMacroScope_1222_,
                                        );
                                        v___x_1231_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__34;
                                        v___x_1232_ =
                                            leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                        leanh::lean_ctor_set(v___x_1232_, 0, v___x_1226_);
                                        leanh::lean_ctor_set(v___x_1232_, 1, v___x_1229_);
                                        leanh::lean_ctor_set(v___x_1232_, 2, v___x_1230_);
                                        leanh::lean_ctor_set(v___x_1232_, 3, v___x_1231_);
                                        v___x_1233_ = l_Lean_Syntax_node1(
                                            v___x_1226_,
                                            v___x_1207_,
                                            v___x_1232_,
                                        );
                                        v___x_1234_ = l_Lean_Syntax_node2(
                                            v___x_1226_,
                                            v___x_1202_,
                                            v___x_1228_,
                                            v___x_1233_,
                                        );
                                        v___x_1235_ = l_Std_Do_termSpred_x28___x29___closed__6;
                                        v___x_1236_ =
                                            leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_1236_, 0, v___x_1226_);
                                        leanh::lean_ctor_set(v___x_1236_, 1, v___x_1235_);
                                        v___x_1237_ = l_Std_Do_termSpred_x28___x29___closed__12;
                                        v___x_1238_ =
                                            leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_1238_, 0, v___x_1226_);
                                        leanh::lean_ctor_set(v___x_1238_, 1, v___x_1237_);
                                        leanh::lean_inc_ref(v___x_1238_);
                                        v___x_1239_ = l_Lean_Syntax_node3(
                                            v___x_1226_,
                                            v___x_1183_,
                                            v___x_1236_,
                                            v___x_1224_,
                                            v___x_1238_,
                                        );
                                        v___x_1240_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__35;
                                        v___x_1241_ =
                                            leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_1241_, 0, v___x_1226_);
                                        leanh::lean_ctor_set(v___x_1241_, 1, v___x_1240_);
                                        v___x_1242_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37;
                                        v___x_1243_ = l_Lean_Syntax_node1(
                                            v___x_1226_,
                                            v___x_1242_,
                                            v___x_1225_,
                                        );
                                        v___x_1244_ = l_Lean_Syntax_node5(
                                            v___x_1226_,
                                            v___x_1197_,
                                            v___x_1234_,
                                            v___x_1239_,
                                            v___x_1241_,
                                            v___x_1243_,
                                            v___x_1238_,
                                        );
                                        v___x_1245_ =
                                            leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_1245_, 0, v___x_1244_);
                                        leanh::lean_ctor_set(v___x_1245_, 1, v_a_1182_);
                                        return v___x_1245_;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    let mut v_ref_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v_ref_1246_ = leanh::lean_ctor_get(v_a_1181_, 5);
                    v___x_1247_ = l_Lean_Syntax_getArg(v___x_1189_, v___x_1188_);
                    v___x_1248_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1249_ = l_Lean_Syntax_getArg(v___x_1189_, v___x_1248_);
                    v___x_1250_ = leanh::lean_unsigned_to_nat(5);
                    v___x_1251_ = l_Lean_Syntax_getArg(v___x_1189_, v___x_1250_);
                    leanh::lean_dec(v___x_1189_);
                    v___x_1252_ = l_Lean_SourceInfo_fromRef(v_ref_1246_, v___x_1194_);
                    v___x_1253_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__38;
                    leanh::lean_inc_n(v___x_1252_, 7);
                    v___x_1254_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1254_, 0, v___x_1252_);
                    leanh::lean_ctor_set(v___x_1254_, 1, v___x_1253_);
                    v___x_1255_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__39;
                    v___x_1256_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1256_, 0, v___x_1252_);
                    leanh::lean_ctor_set(v___x_1256_, 1, v___x_1255_);
                    v___x_1257_ = l_Std_Do_termSpred_x28___x29___closed__6;
                    v___x_1258_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1258_, 0, v___x_1252_);
                    leanh::lean_ctor_set(v___x_1258_, 1, v___x_1257_);
                    v___x_1259_ = l_Std_Do_termSpred_x28___x29___closed__12;
                    v___x_1260_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1260_, 0, v___x_1252_);
                    leanh::lean_ctor_set(v___x_1260_, 1, v___x_1259_);
                    leanh::lean_inc_ref(v___x_1260_);
                    leanh::lean_inc_ref(v___x_1258_);
                    v___x_1261_ = l_Lean_Syntax_node3(
                        v___x_1252_,
                        v___x_1183_,
                        v___x_1258_,
                        v___x_1249_,
                        v___x_1260_,
                    );
                    v___x_1262_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__40;
                    v___x_1263_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1263_, 0, v___x_1252_);
                    leanh::lean_ctor_set(v___x_1263_, 1, v___x_1262_);
                    v___x_1264_ = l_Lean_Syntax_node3(
                        v___x_1252_,
                        v___x_1183_,
                        v___x_1258_,
                        v___x_1251_,
                        v___x_1260_,
                    );
                    v___x_1265_ = l_Lean_Syntax_node6(
                        v___x_1252_,
                        v___x_1195_,
                        v___x_1254_,
                        v___x_1247_,
                        v___x_1256_,
                        v___x_1261_,
                        v___x_1263_,
                        v___x_1264_,
                    );
                    v___x_1266_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1266_, 0, v___x_1265_);
                    leanh::lean_ctor_set(v___x_1266_, 1, v_a_1182_);
                    return v___x_1266_;
                }
            } else {
                let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1269_: u8 = 0;
                v___x_1267_ = l_Lean_Syntax_getArg(v___x_1189_, v___x_1188_);
                leanh::lean_dec(v___x_1189_);
                v___x_1268_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42;
                leanh::lean_inc(v___x_1267_);
                v___x_1269_ = l_Lean_Syntax_isOfKind(v___x_1267_, v___x_1268_);
                if v___x_1269_ == 0 {
                    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v___x_1267_);
                    v___x_1270_ = leanh::lean_box(1);
                    v___x_1271_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1271_, 0, v___x_1270_);
                    leanh::lean_ctor_set(v___x_1271_, 1, v_a_1182_);
                    return v___x_1271_;
                } else {
                    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1273_: u8 = 0;
                    v___x_1272_ = l_Lean_Syntax_getArg(v___x_1267_, v___x_1188_);
                    v___x_1273_ = l_Lean_Syntax_matchesNull(v___x_1272_, v___x_1187_);
                    if v___x_1273_ == 0 {
                        let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
                        leanh::lean_dec(v___x_1267_);
                        v___x_1274_ = leanh::lean_box(1);
                        v___x_1275_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1275_, 0, v___x_1274_);
                        leanh::lean_ctor_set(v___x_1275_, 1, v_a_1182_);
                        return v___x_1275_;
                    } else {
                        let mut v_ref_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_xs_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                        v_ref_1276_ = leanh::lean_ctor_get(v_a_1181_, 5);
                        v___x_1277_ = l_Lean_Syntax_getArg(v___x_1267_, v___x_1187_);
                        v___x_1278_ = leanh::lean_unsigned_to_nat(3);
                        v___x_1279_ = l_Lean_Syntax_getArg(v___x_1267_, v___x_1278_);
                        leanh::lean_dec(v___x_1267_);
                        v_xs_1280_ = l_Lean_Syntax_getArgs(v___x_1277_);
                        leanh::lean_dec(v___x_1277_);
                        v___x_1281_ = l_Lean_SourceInfo_fromRef(v_ref_1276_, v___x_1191_);
                        leanh::lean_inc_n(v___x_1281_, 8);
                        v___x_1282_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1282_, 0, v___x_1281_);
                        leanh::lean_ctor_set(v___x_1282_, 1, v___x_1192_);
                        v___x_1283_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37;
                        v___x_1284_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43_once), _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43);
                        v___x_1285_ = l_Array_append___redArg(v___x_1284_, v_xs_1280_);
                        leanh::lean_dec_ref(v_xs_1280_);
                        v___x_1286_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_1286_, 0, v___x_1281_);
                        leanh::lean_ctor_set(v___x_1286_, 1, v___x_1283_);
                        leanh::lean_ctor_set(v___x_1286_, 2, v___x_1285_);
                        v___x_1287_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_1287_, 0, v___x_1281_);
                        leanh::lean_ctor_set(v___x_1287_, 1, v___x_1283_);
                        leanh::lean_ctor_set(v___x_1287_, 2, v___x_1284_);
                        v___x_1288_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__44;
                        v___x_1289_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1289_, 0, v___x_1281_);
                        leanh::lean_ctor_set(v___x_1289_, 1, v___x_1288_);
                        v___x_1290_ = l_Std_Do_termSpred_x28___x29___closed__6;
                        v___x_1291_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1291_, 0, v___x_1281_);
                        leanh::lean_ctor_set(v___x_1291_, 1, v___x_1290_);
                        v___x_1292_ = l_Std_Do_termSpred_x28___x29___closed__12;
                        v___x_1293_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1293_, 0, v___x_1281_);
                        leanh::lean_ctor_set(v___x_1293_, 1, v___x_1292_);
                        v___x_1294_ = l_Lean_Syntax_node3(
                            v___x_1281_,
                            v___x_1183_,
                            v___x_1291_,
                            v___x_1279_,
                            v___x_1293_,
                        );
                        v___x_1295_ = l_Lean_Syntax_node4(
                            v___x_1281_,
                            v___x_1268_,
                            v___x_1286_,
                            v___x_1287_,
                            v___x_1289_,
                            v___x_1294_,
                        );
                        v___x_1296_ =
                            l_Lean_Syntax_node2(v___x_1281_, v___x_1193_, v___x_1282_, v___x_1295_);
                        v___x_1297_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1297_, 0, v___x_1296_);
                        leanh::lean_ctor_set(v___x_1297_, 1, v_a_1182_);
                        return v___x_1297_;
                    }
                }
            }
        } else {
            let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1300_: u8 = 0;
            v___x_1298_ = l_Lean_Syntax_getArg(v___x_1189_, v___x_1187_);
            v___x_1299_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12;
            leanh::lean_inc(v___x_1298_);
            v___x_1300_ = l_Lean_Syntax_isOfKind(v___x_1298_, v___x_1299_);
            if v___x_1300_ == 0 {
                let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_1298_);
                leanh::lean_dec(v___x_1189_);
                v___x_1301_ = leanh::lean_box(1);
                v___x_1302_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1302_, 0, v___x_1301_);
                leanh::lean_ctor_set(v___x_1302_, 1, v_a_1182_);
                return v___x_1302_;
            } else {
                let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1305_: u8 = 0;
                v___x_1303_ = l_Lean_Syntax_getArg(v___x_1298_, v___x_1188_);
                leanh::lean_dec(v___x_1298_);
                v___x_1304_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14;
                leanh::lean_inc(v___x_1303_);
                v___x_1305_ = l_Lean_Syntax_isOfKind(v___x_1303_, v___x_1304_);
                if v___x_1305_ == 0 {
                    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v___x_1303_);
                    leanh::lean_dec(v___x_1189_);
                    v___x_1306_ = leanh::lean_box(1);
                    v___x_1307_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1307_, 0, v___x_1306_);
                    leanh::lean_ctor_set(v___x_1307_, 1, v_a_1182_);
                    return v___x_1307_;
                } else {
                    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1310_: u8 = 0;
                    v___x_1308_ = l_Lean_Syntax_getArg(v___x_1303_, v___x_1187_);
                    leanh::lean_dec(v___x_1303_);
                    v___x_1309_ = leanh::lean_box(0);
                    v___x_1310_ = l_Lean_Syntax_matchesIdent(v___x_1308_, v___x_1309_);
                    leanh::lean_dec(v___x_1308_);
                    if v___x_1310_ == 0 {
                        let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
                        leanh::lean_dec(v___x_1189_);
                        v___x_1311_ = leanh::lean_box(1);
                        v___x_1312_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1312_, 0, v___x_1311_);
                        leanh::lean_ctor_set(v___x_1312_, 1, v_a_1182_);
                        return v___x_1312_;
                    } else {
                        let mut v_quotContext_1313_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_currMacroScope_1314_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_ref_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1317_: u8 = 0;
                        let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_quotContext_1313_ = leanh::lean_ctor_get(v_a_1181_, 1);
                        v_currMacroScope_1314_ = leanh::lean_ctor_get(v_a_1181_, 2);
                        v_ref_1315_ = leanh::lean_ctor_get(v_a_1181_, 5);
                        v___x_1316_ = l_Lean_Syntax_getArg(v___x_1189_, v___x_1188_);
                        leanh::lean_dec(v___x_1189_);
                        v___x_1317_ = 0;
                        v___x_1318_ = l_Lean_SourceInfo_fromRef(v_ref_1315_, v___x_1317_);
                        v___x_1319_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15;
                        leanh::lean_inc_n(v___x_1318_, 7);
                        v___x_1320_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1320_, 0, v___x_1318_);
                        leanh::lean_ctor_set(v___x_1320_, 1, v___x_1319_);
                        v___x_1321_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17_once), _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17);
                        leanh::lean_inc(v_currMacroScope_1314_);
                        leanh::lean_inc(v_quotContext_1313_);
                        v___x_1322_ = l_Lean_addMacroScope(
                            v_quotContext_1313_,
                            v___x_1309_,
                            v_currMacroScope_1314_,
                        );
                        v___x_1323_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__34;
                        v___x_1324_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                        leanh::lean_ctor_set(v___x_1324_, 0, v___x_1318_);
                        leanh::lean_ctor_set(v___x_1324_, 1, v___x_1321_);
                        leanh::lean_ctor_set(v___x_1324_, 2, v___x_1322_);
                        leanh::lean_ctor_set(v___x_1324_, 3, v___x_1323_);
                        v___x_1325_ = l_Lean_Syntax_node1(v___x_1318_, v___x_1304_, v___x_1324_);
                        v___x_1326_ =
                            l_Lean_Syntax_node2(v___x_1318_, v___x_1299_, v___x_1320_, v___x_1325_);
                        v___x_1327_ = l_Std_Do_termSpred_x28___x29___closed__6;
                        v___x_1328_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1328_, 0, v___x_1318_);
                        leanh::lean_ctor_set(v___x_1328_, 1, v___x_1327_);
                        v___x_1329_ = l_Std_Do_termSpred_x28___x29___closed__12;
                        v___x_1330_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1330_, 0, v___x_1318_);
                        leanh::lean_ctor_set(v___x_1330_, 1, v___x_1329_);
                        leanh::lean_inc_ref(v___x_1330_);
                        v___x_1331_ = l_Lean_Syntax_node3(
                            v___x_1318_,
                            v___x_1183_,
                            v___x_1328_,
                            v___x_1316_,
                            v___x_1330_,
                        );
                        v___x_1332_ = l_Lean_Syntax_node3(
                            v___x_1318_,
                            v___x_1190_,
                            v___x_1326_,
                            v___x_1331_,
                            v___x_1330_,
                        );
                        v___x_1333_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1333_, 0, v___x_1332_);
                        leanh::lean_ctor_set(v___x_1333_, 1, v_a_1182_);
                        return v___x_1333_;
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___boxed(
    mut v_x_1334_: *mut leanh::LeanObject,
    mut v_a_1335_: *mut leanh::LeanObject,
    mut v_a_1336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1337_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2(v_x_1334_, v_a_1335_, v_a_1336_);
    leanh::lean_dec_ref(v_a_1335_);
    return v_res_1337_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__0(
    mut v_toPure_1338_: *mut leanh::LeanObject,
    mut v_x_1339_: *mut leanh::LeanObject,
    mut v_quotCtx_1340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1341_ = leanh::lean_apply_2(v_toPure_1338_, leanh::lean_box(0), v_x_1339_);
    return v___x_1341_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed(
    mut v_toPure_1342_: *mut leanh::LeanObject,
    mut v_x_1343_: *mut leanh::LeanObject,
    mut v_quotCtx_1344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1345_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__0(
        v_toPure_1342_,
        v_x_1343_,
        v_quotCtx_1344_,
    );
    leanh::lean_dec(v_quotCtx_1344_);
    return v_res_1345_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__1(
    mut v_inst_1346_: *mut leanh::LeanObject,
    mut v_toBind_1347_: *mut leanh::LeanObject,
    mut v___f_1348_: *mut leanh::LeanObject,
    mut v_scp_1349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getContext_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getContext_1350_ = leanh::lean_ctor_get(v_inst_1346_, 2);
    leanh::lean_inc(v_getContext_1350_);
    leanh::lean_dec_ref(v_inst_1346_);
    v___x_1351_ = leanh::lean_apply_4(
        v_toBind_1347_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getContext_1350_,
        v___f_1348_,
    );
    return v___x_1351_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed(
    mut v_inst_1352_: *mut leanh::LeanObject,
    mut v_toBind_1353_: *mut leanh::LeanObject,
    mut v___f_1354_: *mut leanh::LeanObject,
    mut v_scp_1355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1356_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__1(
        v_inst_1352_,
        v_toBind_1353_,
        v___f_1354_,
        v_scp_1355_,
    );
    leanh::lean_dec(v_scp_1355_);
    return v_res_1356_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__2(
    mut v_inst_1357_: *mut leanh::LeanObject,
    mut v_toBind_1358_: *mut leanh::LeanObject,
    mut v___f_1359_: *mut leanh::LeanObject,
    mut v_info_1360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getCurrMacroScope_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getCurrMacroScope_1361_ = leanh::lean_ctor_get(v_inst_1357_, 1);
    leanh::lean_inc(v_getCurrMacroScope_1361_);
    leanh::lean_dec_ref(v_inst_1357_);
    v___x_1362_ = leanh::lean_apply_4(
        v_toBind_1358_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getCurrMacroScope_1361_,
        v___f_1359_,
    );
    return v___x_1362_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed(
    mut v_inst_1363_: *mut leanh::LeanObject,
    mut v_toBind_1364_: *mut leanh::LeanObject,
    mut v___f_1365_: *mut leanh::LeanObject,
    mut v_info_1366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1367_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__2(
        v_inst_1363_,
        v_toBind_1364_,
        v___f_1365_,
        v_info_1366_,
    );
    leanh::lean_dec(v_info_1366_);
    return v_res_1367_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__3(
    mut v___x_1368_: u8,
    mut v_toPure_1369_: *mut leanh::LeanObject,
    mut v_____do__lift_1370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1371_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1370_, v___x_1368_);
    v___x_1372_ =
        leanh::lean_apply_2(v_toPure_1369_, leanh::lean_box(0), v___x_1371_);
    return v___x_1372_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed(
    mut v___x_1373_: *mut leanh::LeanObject,
    mut v_toPure_1374_: *mut leanh::LeanObject,
    mut v_____do__lift_1375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9844__boxed_1376_: u8 = 0;
    let mut v_res_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9844__boxed_1376_ = (leanh::lean_unbox(v___x_1373_) as u8);
    v_res_1377_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__3(
        v___x_9844__boxed_1376_,
        v_toPure_1374_,
        v_____do__lift_1375_,
    );
    leanh::lean_dec(v_____do__lift_1375_);
    return v_res_1377_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__20(
    mut v_info_1380_: *mut leanh::LeanObject,
    mut v___x_1381_: *mut leanh::LeanObject,
    mut v_scp_1382_: *mut leanh::LeanObject,
    mut v___x_1383_: *mut leanh::LeanObject,
    mut v___x_1384_: *mut leanh::LeanObject,
    mut v___x_1385_: *mut leanh::LeanObject,
    mut v___x_1386_: *mut leanh::LeanObject,
    mut v___x_1387_: *mut leanh::LeanObject,
    mut v___x_1388_: *mut leanh::LeanObject,
    mut v___x_1389_: *mut leanh::LeanObject,
    mut v___x_1390_: *mut leanh::LeanObject,
    mut v_____do__lift_1391_: *mut leanh::LeanObject,
    mut v_toPure_1392_: *mut leanh::LeanObject,
    mut v_quotCtx_1393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1394_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15;
    leanh::lean_inc_n(v_info_1380_, 7);
    v___x_1395_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1395_, 0, v_info_1380_);
    leanh::lean_ctor_set(v___x_1395_, 1, v___x_1394_);
    v___x_1396_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17_once), _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17);
    v___x_1397_ = l_Lean_addMacroScope(v_quotCtx_1393_, v___x_1381_, v_scp_1382_);
    v___x_1398_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__0;
    v___x_1399_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__1;
    v___x_1400_ = l_Lean_Name_mkStr4(v___x_1383_, v___x_1384_, v___x_1398_, v___x_1399_);
    v___x_1401_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1401_, 0, v___x_1400_);
    v___x_1402_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20;
    leanh::lean_inc_ref_n(v___x_1385_, 3);
    v___x_1403_ = l_Lean_Name_mkStr2(v___x_1385_, v___x_1402_);
    v___x_1404_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1404_, 0, v___x_1403_);
    v___x_1405_ = l_Lean_Name_mkStr2(v___x_1385_, v___x_1386_);
    v___x_1406_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1406_, 0, v___x_1405_);
    v___x_1407_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25;
    v___x_1408_ = l_Lean_Name_mkStr2(v___x_1385_, v___x_1407_);
    v___x_1409_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1409_, 0, v___x_1408_);
    v___x_1410_ = l_Lean_Name_mkStr1(v___x_1385_);
    v___x_1411_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1411_, 0, v___x_1410_);
    v___x_1412_ = leanh::lean_box(0);
    v___x_1413_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1413_, 0, v___x_1411_);
    leanh::lean_ctor_set(v___x_1413_, 1, v___x_1412_);
    v___x_1414_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1414_, 0, v___x_1409_);
    leanh::lean_ctor_set(v___x_1414_, 1, v___x_1413_);
    v___x_1415_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1415_, 0, v___x_1406_);
    leanh::lean_ctor_set(v___x_1415_, 1, v___x_1414_);
    v___x_1416_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1416_, 0, v___x_1404_);
    leanh::lean_ctor_set(v___x_1416_, 1, v___x_1415_);
    v___x_1417_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1417_, 0, v___x_1401_);
    leanh::lean_ctor_set(v___x_1417_, 1, v___x_1416_);
    v___x_1418_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1418_, 0, v_info_1380_);
    leanh::lean_ctor_set(v___x_1418_, 1, v___x_1396_);
    leanh::lean_ctor_set(v___x_1418_, 2, v___x_1397_);
    leanh::lean_ctor_set(v___x_1418_, 3, v___x_1417_);
    v___x_1419_ = l_Lean_Syntax_node1(v_info_1380_, v___x_1387_, v___x_1418_);
    v___x_1420_ = l_Lean_Syntax_node2(v_info_1380_, v___x_1388_, v___x_1395_, v___x_1419_);
    v___x_1421_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__35;
    v___x_1422_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1422_, 0, v_info_1380_);
    leanh::lean_ctor_set(v___x_1422_, 1, v___x_1421_);
    v___x_1423_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37;
    v___x_1424_ = l_Lean_Syntax_node1(v_info_1380_, v___x_1423_, v___x_1389_);
    v___x_1425_ = l_Std_Do_termSpred_x28___x29___closed__12;
    v___x_1426_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1426_, 0, v_info_1380_);
    leanh::lean_ctor_set(v___x_1426_, 1, v___x_1425_);
    v___x_1427_ = l_Lean_Syntax_node5(
        v_info_1380_,
        v___x_1390_,
        v___x_1420_,
        v_____do__lift_1391_,
        v___x_1422_,
        v___x_1424_,
        v___x_1426_,
    );
    v___x_1428_ =
        leanh::lean_apply_2(v_toPure_1392_, leanh::lean_box(0), v___x_1427_);
    return v___x_1428_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__4(
    mut v_info_1429_: *mut leanh::LeanObject,
    mut v___x_1430_: *mut leanh::LeanObject,
    mut v___x_1431_: *mut leanh::LeanObject,
    mut v___x_1432_: *mut leanh::LeanObject,
    mut v___x_1433_: *mut leanh::LeanObject,
    mut v___x_1434_: *mut leanh::LeanObject,
    mut v___x_1435_: *mut leanh::LeanObject,
    mut v___x_1436_: *mut leanh::LeanObject,
    mut v___x_1437_: *mut leanh::LeanObject,
    mut v___x_1438_: *mut leanh::LeanObject,
    mut v_____do__lift_1439_: *mut leanh::LeanObject,
    mut v_toPure_1440_: *mut leanh::LeanObject,
    mut v_toBind_1441_: *mut leanh::LeanObject,
    mut v_getContext_1442_: *mut leanh::LeanObject,
    mut v_scp_1443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1444_ = leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__20 as *mut core::ffi::c_void,
        14,
        13,
    );
    leanh::lean_closure_set(v___f_1444_, 0, v_info_1429_);
    leanh::lean_closure_set(v___f_1444_, 1, v___x_1430_);
    leanh::lean_closure_set(v___f_1444_, 2, v_scp_1443_);
    leanh::lean_closure_set(v___f_1444_, 3, v___x_1431_);
    leanh::lean_closure_set(v___f_1444_, 4, v___x_1432_);
    leanh::lean_closure_set(v___f_1444_, 5, v___x_1433_);
    leanh::lean_closure_set(v___f_1444_, 6, v___x_1434_);
    leanh::lean_closure_set(v___f_1444_, 7, v___x_1435_);
    leanh::lean_closure_set(v___f_1444_, 8, v___x_1436_);
    leanh::lean_closure_set(v___f_1444_, 9, v___x_1437_);
    leanh::lean_closure_set(v___f_1444_, 10, v___x_1438_);
    leanh::lean_closure_set(v___f_1444_, 11, v_____do__lift_1439_);
    leanh::lean_closure_set(v___f_1444_, 12, v_toPure_1440_);
    v___x_1445_ = leanh::lean_apply_4(
        v_toBind_1441_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getContext_1442_,
        v___f_1444_,
    );
    return v___x_1445_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__5(
    mut v_inst_1446_: *mut leanh::LeanObject,
    mut v___x_1447_: *mut leanh::LeanObject,
    mut v___x_1448_: *mut leanh::LeanObject,
    mut v___x_1449_: *mut leanh::LeanObject,
    mut v___x_1450_: *mut leanh::LeanObject,
    mut v___x_1451_: *mut leanh::LeanObject,
    mut v___x_1452_: *mut leanh::LeanObject,
    mut v___x_1453_: *mut leanh::LeanObject,
    mut v___x_1454_: *mut leanh::LeanObject,
    mut v___x_1455_: *mut leanh::LeanObject,
    mut v_____do__lift_1456_: *mut leanh::LeanObject,
    mut v_toPure_1457_: *mut leanh::LeanObject,
    mut v_toBind_1458_: *mut leanh::LeanObject,
    mut v_info_1459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getCurrMacroScope_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getContext_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getCurrMacroScope_1460_ = leanh::lean_ctor_get(v_inst_1446_, 1);
    leanh::lean_inc(v_getCurrMacroScope_1460_);
    v_getContext_1461_ = leanh::lean_ctor_get(v_inst_1446_, 2);
    leanh::lean_inc(v_getContext_1461_);
    leanh::lean_dec_ref(v_inst_1446_);
    leanh::lean_inc(v_toBind_1458_);
    v___f_1462_ = leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__4 as *mut core::ffi::c_void,
        15,
        14,
    );
    leanh::lean_closure_set(v___f_1462_, 0, v_info_1459_);
    leanh::lean_closure_set(v___f_1462_, 1, v___x_1447_);
    leanh::lean_closure_set(v___f_1462_, 2, v___x_1448_);
    leanh::lean_closure_set(v___f_1462_, 3, v___x_1449_);
    leanh::lean_closure_set(v___f_1462_, 4, v___x_1450_);
    leanh::lean_closure_set(v___f_1462_, 5, v___x_1451_);
    leanh::lean_closure_set(v___f_1462_, 6, v___x_1452_);
    leanh::lean_closure_set(v___f_1462_, 7, v___x_1453_);
    leanh::lean_closure_set(v___f_1462_, 8, v___x_1454_);
    leanh::lean_closure_set(v___f_1462_, 9, v___x_1455_);
    leanh::lean_closure_set(v___f_1462_, 10, v_____do__lift_1456_);
    leanh::lean_closure_set(v___f_1462_, 11, v_toPure_1457_);
    leanh::lean_closure_set(v___f_1462_, 12, v_toBind_1458_);
    leanh::lean_closure_set(v___f_1462_, 13, v_getContext_1461_);
    v___x_1463_ = leanh::lean_apply_4(
        v_toBind_1458_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getCurrMacroScope_1460_,
        v___f_1462_,
    );
    return v___x_1463_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__7(
    mut v_inst_1464_: *mut leanh::LeanObject,
    mut v_toApplicative_1465_: *mut leanh::LeanObject,
    mut v_inst_1466_: *mut leanh::LeanObject,
    mut v___x_1467_: *mut leanh::LeanObject,
    mut v___x_1468_: *mut leanh::LeanObject,
    mut v___x_1469_: *mut leanh::LeanObject,
    mut v___x_1470_: *mut leanh::LeanObject,
    mut v___x_1471_: *mut leanh::LeanObject,
    mut v___x_1472_: *mut leanh::LeanObject,
    mut v___x_1473_: *mut leanh::LeanObject,
    mut v___x_1474_: *mut leanh::LeanObject,
    mut v___x_1475_: *mut leanh::LeanObject,
    mut v_toBind_1476_: *mut leanh::LeanObject,
    mut v___x_1477_: u8,
    mut v_____do__lift_1478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getRef_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getRef_1479_ = leanh::lean_ctor_get(v_inst_1464_, 0);
    leanh::lean_inc(v_getRef_1479_);
    leanh::lean_dec_ref(v_inst_1464_);
    v_toPure_1480_ = leanh::lean_ctor_get(v_toApplicative_1465_, 1);
    leanh::lean_inc_n(v_toPure_1480_, 2);
    leanh::lean_dec_ref(v_toApplicative_1465_);
    leanh::lean_inc_n(v_toBind_1476_, 2);
    v___f_1481_ = leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__5 as *mut core::ffi::c_void,
        14,
        13,
    );
    leanh::lean_closure_set(v___f_1481_, 0, v_inst_1466_);
    leanh::lean_closure_set(v___f_1481_, 1, v___x_1467_);
    leanh::lean_closure_set(v___f_1481_, 2, v___x_1468_);
    leanh::lean_closure_set(v___f_1481_, 3, v___x_1469_);
    leanh::lean_closure_set(v___f_1481_, 4, v___x_1470_);
    leanh::lean_closure_set(v___f_1481_, 5, v___x_1471_);
    leanh::lean_closure_set(v___f_1481_, 6, v___x_1472_);
    leanh::lean_closure_set(v___f_1481_, 7, v___x_1473_);
    leanh::lean_closure_set(v___f_1481_, 8, v___x_1474_);
    leanh::lean_closure_set(v___f_1481_, 9, v___x_1475_);
    leanh::lean_closure_set(v___f_1481_, 10, v_____do__lift_1478_);
    leanh::lean_closure_set(v___f_1481_, 11, v_toPure_1480_);
    leanh::lean_closure_set(v___f_1481_, 12, v_toBind_1476_);
    v___x_1482_ = leanh::lean_box((v___x_1477_) as usize);
    v___f_1483_ = leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1483_, 0, v___x_1482_);
    leanh::lean_closure_set(v___f_1483_, 1, v_toPure_1480_);
    v___x_1484_ = leanh::lean_apply_4(
        v_toBind_1476_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRef_1479_,
        v___f_1483_,
    );
    v___x_1485_ = leanh::lean_apply_4(
        v_toBind_1476_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1484_,
        v___f_1481_,
    );
    return v___x_1485_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__7___boxed(
    mut v_inst_1486_: *mut leanh::LeanObject,
    mut v_toApplicative_1487_: *mut leanh::LeanObject,
    mut v_inst_1488_: *mut leanh::LeanObject,
    mut v___x_1489_: *mut leanh::LeanObject,
    mut v___x_1490_: *mut leanh::LeanObject,
    mut v___x_1491_: *mut leanh::LeanObject,
    mut v___x_1492_: *mut leanh::LeanObject,
    mut v___x_1493_: *mut leanh::LeanObject,
    mut v___x_1494_: *mut leanh::LeanObject,
    mut v___x_1495_: *mut leanh::LeanObject,
    mut v___x_1496_: *mut leanh::LeanObject,
    mut v___x_1497_: *mut leanh::LeanObject,
    mut v_toBind_1498_: *mut leanh::LeanObject,
    mut v___x_1499_: *mut leanh::LeanObject,
    mut v_____do__lift_1500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10034__boxed_1501_: u8 = 0;
    let mut v_res_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10034__boxed_1501_ = (leanh::lean_unbox(v___x_1499_) as u8);
    v_res_1502_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__7(
        v_inst_1486_,
        v_toApplicative_1487_,
        v_inst_1488_,
        v___x_1489_,
        v___x_1490_,
        v___x_1491_,
        v___x_1492_,
        v___x_1493_,
        v___x_1494_,
        v___x_1495_,
        v___x_1496_,
        v___x_1497_,
        v_toBind_1498_,
        v___x_10034__boxed_1501_,
        v_____do__lift_1500_,
    );
    return v_res_1502_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__15(
    mut v_info_1503_: *mut leanh::LeanObject,
    mut v___x_1504_: *mut leanh::LeanObject,
    mut v_xs_1505_: *mut leanh::LeanObject,
    mut v___x_1506_: *mut leanh::LeanObject,
    mut v_b_1507_: *mut leanh::LeanObject,
    mut v___x_1508_: *mut leanh::LeanObject,
    mut v_toPure_1509_: *mut leanh::LeanObject,
    mut v_quotCtx_1510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_n(v_info_1503_, 5);
    v___x_1511_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1511_, 0, v_info_1503_);
    leanh::lean_ctor_set(v___x_1511_, 1, v___x_1504_);
    v___x_1512_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37;
    v___x_1513_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43_once), _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43);
    v___x_1514_ = l_Array_append___redArg(v___x_1513_, v_xs_1505_);
    v___x_1515_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1515_, 0, v_info_1503_);
    leanh::lean_ctor_set(v___x_1515_, 1, v___x_1512_);
    leanh::lean_ctor_set(v___x_1515_, 2, v___x_1514_);
    v___x_1516_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1516_, 0, v_info_1503_);
    leanh::lean_ctor_set(v___x_1516_, 1, v___x_1512_);
    leanh::lean_ctor_set(v___x_1516_, 2, v___x_1513_);
    v___x_1517_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__44;
    v___x_1518_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1518_, 0, v_info_1503_);
    leanh::lean_ctor_set(v___x_1518_, 1, v___x_1517_);
    v___x_1519_ = l_Lean_Syntax_node4(
        v_info_1503_,
        v___x_1506_,
        v___x_1515_,
        v___x_1516_,
        v___x_1518_,
        v_b_1507_,
    );
    v___x_1520_ = l_Lean_Syntax_node2(v_info_1503_, v___x_1508_, v___x_1511_, v___x_1519_);
    v___x_1521_ =
        leanh::lean_apply_2(v_toPure_1509_, leanh::lean_box(0), v___x_1520_);
    return v___x_1521_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__15___boxed(
    mut v_info_1522_: *mut leanh::LeanObject,
    mut v___x_1523_: *mut leanh::LeanObject,
    mut v_xs_1524_: *mut leanh::LeanObject,
    mut v___x_1525_: *mut leanh::LeanObject,
    mut v_b_1526_: *mut leanh::LeanObject,
    mut v___x_1527_: *mut leanh::LeanObject,
    mut v_toPure_1528_: *mut leanh::LeanObject,
    mut v_quotCtx_1529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1530_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__15(
        v_info_1522_,
        v___x_1523_,
        v_xs_1524_,
        v___x_1525_,
        v_b_1526_,
        v___x_1527_,
        v_toPure_1528_,
        v_quotCtx_1529_,
    );
    leanh::lean_dec(v_quotCtx_1529_);
    leanh::lean_dec_ref(v_xs_1524_);
    return v_res_1530_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__6(
    mut v_toBind_1531_: *mut leanh::LeanObject,
    mut v_getContext_1532_: *mut leanh::LeanObject,
    mut v___f_1533_: *mut leanh::LeanObject,
    mut v_scp_1534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1535_ = leanh::lean_apply_4(
        v_toBind_1531_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getContext_1532_,
        v___f_1533_,
    );
    return v___x_1535_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__6___boxed(
    mut v_toBind_1536_: *mut leanh::LeanObject,
    mut v_getContext_1537_: *mut leanh::LeanObject,
    mut v___f_1538_: *mut leanh::LeanObject,
    mut v_scp_1539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1540_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__6(
        v_toBind_1536_,
        v_getContext_1537_,
        v___f_1538_,
        v_scp_1539_,
    );
    leanh::lean_dec(v_scp_1539_);
    return v_res_1540_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__8(
    mut v_inst_1541_: *mut leanh::LeanObject,
    mut v___x_1542_: *mut leanh::LeanObject,
    mut v_xs_1543_: *mut leanh::LeanObject,
    mut v___x_1544_: *mut leanh::LeanObject,
    mut v_b_1545_: *mut leanh::LeanObject,
    mut v___x_1546_: *mut leanh::LeanObject,
    mut v_toPure_1547_: *mut leanh::LeanObject,
    mut v_toBind_1548_: *mut leanh::LeanObject,
    mut v_info_1549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getCurrMacroScope_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getContext_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getCurrMacroScope_1550_ = leanh::lean_ctor_get(v_inst_1541_, 1);
    leanh::lean_inc(v_getCurrMacroScope_1550_);
    v_getContext_1551_ = leanh::lean_ctor_get(v_inst_1541_, 2);
    leanh::lean_inc(v_getContext_1551_);
    leanh::lean_dec_ref(v_inst_1541_);
    v___f_1552_ = leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__15___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_1552_, 0, v_info_1549_);
    leanh::lean_closure_set(v___f_1552_, 1, v___x_1542_);
    leanh::lean_closure_set(v___f_1552_, 2, v_xs_1543_);
    leanh::lean_closure_set(v___f_1552_, 3, v___x_1544_);
    leanh::lean_closure_set(v___f_1552_, 4, v_b_1545_);
    leanh::lean_closure_set(v___f_1552_, 5, v___x_1546_);
    leanh::lean_closure_set(v___f_1552_, 6, v_toPure_1547_);
    leanh::lean_inc(v_toBind_1548_);
    v___f_1553_ = leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__6___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1553_, 0, v_toBind_1548_);
    leanh::lean_closure_set(v___f_1553_, 1, v_getContext_1551_);
    leanh::lean_closure_set(v___f_1553_, 2, v___f_1552_);
    v___x_1554_ = leanh::lean_apply_4(
        v_toBind_1548_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getCurrMacroScope_1550_,
        v___f_1553_,
    );
    return v___x_1554_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__10(
    mut v_inst_1555_: *mut leanh::LeanObject,
    mut v_toApplicative_1556_: *mut leanh::LeanObject,
    mut v_inst_1557_: *mut leanh::LeanObject,
    mut v___x_1558_: *mut leanh::LeanObject,
    mut v_xs_1559_: *mut leanh::LeanObject,
    mut v___x_1560_: *mut leanh::LeanObject,
    mut v___x_1561_: *mut leanh::LeanObject,
    mut v_toBind_1562_: *mut leanh::LeanObject,
    mut v___x_1563_: u8,
    mut v_b_1564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getRef_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getRef_1565_ = leanh::lean_ctor_get(v_inst_1555_, 0);
    leanh::lean_inc(v_getRef_1565_);
    leanh::lean_dec_ref(v_inst_1555_);
    v_toPure_1566_ = leanh::lean_ctor_get(v_toApplicative_1556_, 1);
    leanh::lean_inc_n(v_toPure_1566_, 2);
    leanh::lean_dec_ref(v_toApplicative_1556_);
    leanh::lean_inc_n(v_toBind_1562_, 2);
    v___f_1567_ = leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__8 as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_1567_, 0, v_inst_1557_);
    leanh::lean_closure_set(v___f_1567_, 1, v___x_1558_);
    leanh::lean_closure_set(v___f_1567_, 2, v_xs_1559_);
    leanh::lean_closure_set(v___f_1567_, 3, v___x_1560_);
    leanh::lean_closure_set(v___f_1567_, 4, v_b_1564_);
    leanh::lean_closure_set(v___f_1567_, 5, v___x_1561_);
    leanh::lean_closure_set(v___f_1567_, 6, v_toPure_1566_);
    leanh::lean_closure_set(v___f_1567_, 7, v_toBind_1562_);
    v___x_1568_ = leanh::lean_box((v___x_1563_) as usize);
    v___f_1569_ = leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1569_, 0, v___x_1568_);
    leanh::lean_closure_set(v___f_1569_, 1, v_toPure_1566_);
    v___x_1570_ = leanh::lean_apply_4(
        v_toBind_1562_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRef_1565_,
        v___f_1569_,
    );
    v___x_1571_ = leanh::lean_apply_4(
        v_toBind_1562_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1570_,
        v___f_1567_,
    );
    return v___x_1571_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__10___boxed(
    mut v_inst_1572_: *mut leanh::LeanObject,
    mut v_toApplicative_1573_: *mut leanh::LeanObject,
    mut v_inst_1574_: *mut leanh::LeanObject,
    mut v___x_1575_: *mut leanh::LeanObject,
    mut v_xs_1576_: *mut leanh::LeanObject,
    mut v___x_1577_: *mut leanh::LeanObject,
    mut v___x_1578_: *mut leanh::LeanObject,
    mut v_toBind_1579_: *mut leanh::LeanObject,
    mut v___x_1580_: *mut leanh::LeanObject,
    mut v_b_1581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10144__boxed_1582_: u8 = 0;
    let mut v_res_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10144__boxed_1582_ = (leanh::lean_unbox(v___x_1580_) as u8);
    v_res_1583_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__10(
        v_inst_1572_,
        v_toApplicative_1573_,
        v_inst_1574_,
        v___x_1575_,
        v_xs_1576_,
        v___x_1577_,
        v___x_1578_,
        v_toBind_1579_,
        v___x_10144__boxed_1582_,
        v_b_1581_,
    );
    return v_res_1583_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__9(
    mut v_info_1584_: *mut leanh::LeanObject,
    mut v___x_1585_: *mut leanh::LeanObject,
    mut v___x_1586_: *mut leanh::LeanObject,
    mut v_t_1587_: *mut leanh::LeanObject,
    mut v_e_1588_: *mut leanh::LeanObject,
    mut v_toPure_1589_: *mut leanh::LeanObject,
    mut v_quotCtx_1590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1591_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__38;
    leanh::lean_inc_n(v_info_1584_, 3);
    v___x_1592_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1592_, 0, v_info_1584_);
    leanh::lean_ctor_set(v___x_1592_, 1, v___x_1591_);
    v___x_1593_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__39;
    v___x_1594_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1594_, 0, v_info_1584_);
    leanh::lean_ctor_set(v___x_1594_, 1, v___x_1593_);
    v___x_1595_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__40;
    v___x_1596_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1596_, 0, v_info_1584_);
    leanh::lean_ctor_set(v___x_1596_, 1, v___x_1595_);
    v___x_1597_ = l_Lean_Syntax_node6(
        v_info_1584_,
        v___x_1585_,
        v___x_1592_,
        v___x_1586_,
        v___x_1594_,
        v_t_1587_,
        v___x_1596_,
        v_e_1588_,
    );
    v___x_1598_ =
        leanh::lean_apply_2(v_toPure_1589_, leanh::lean_box(0), v___x_1597_);
    return v___x_1598_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__9___boxed(
    mut v_info_1599_: *mut leanh::LeanObject,
    mut v___x_1600_: *mut leanh::LeanObject,
    mut v___x_1601_: *mut leanh::LeanObject,
    mut v_t_1602_: *mut leanh::LeanObject,
    mut v_e_1603_: *mut leanh::LeanObject,
    mut v_toPure_1604_: *mut leanh::LeanObject,
    mut v_quotCtx_1605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1606_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__9(
        v_info_1599_,
        v___x_1600_,
        v___x_1601_,
        v_t_1602_,
        v_e_1603_,
        v_toPure_1604_,
        v_quotCtx_1605_,
    );
    leanh::lean_dec(v_quotCtx_1605_);
    return v_res_1606_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__12(
    mut v_inst_1607_: *mut leanh::LeanObject,
    mut v___x_1608_: *mut leanh::LeanObject,
    mut v___x_1609_: *mut leanh::LeanObject,
    mut v_t_1610_: *mut leanh::LeanObject,
    mut v_e_1611_: *mut leanh::LeanObject,
    mut v_toPure_1612_: *mut leanh::LeanObject,
    mut v_toBind_1613_: *mut leanh::LeanObject,
    mut v_info_1614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getCurrMacroScope_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getContext_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getCurrMacroScope_1615_ = leanh::lean_ctor_get(v_inst_1607_, 1);
    leanh::lean_inc(v_getCurrMacroScope_1615_);
    v_getContext_1616_ = leanh::lean_ctor_get(v_inst_1607_, 2);
    leanh::lean_inc(v_getContext_1616_);
    leanh::lean_dec_ref(v_inst_1607_);
    v___f_1617_ = leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__9___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_1617_, 0, v_info_1614_);
    leanh::lean_closure_set(v___f_1617_, 1, v___x_1608_);
    leanh::lean_closure_set(v___f_1617_, 2, v___x_1609_);
    leanh::lean_closure_set(v___f_1617_, 3, v_t_1610_);
    leanh::lean_closure_set(v___f_1617_, 4, v_e_1611_);
    leanh::lean_closure_set(v___f_1617_, 5, v_toPure_1612_);
    leanh::lean_inc(v_toBind_1613_);
    v___f_1618_ = leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__6___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1618_, 0, v_toBind_1613_);
    leanh::lean_closure_set(v___f_1618_, 1, v_getContext_1616_);
    leanh::lean_closure_set(v___f_1618_, 2, v___f_1617_);
    v___x_1619_ = leanh::lean_apply_4(
        v_toBind_1613_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getCurrMacroScope_1615_,
        v___f_1618_,
    );
    return v___x_1619_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__13(
    mut v_inst_1620_: *mut leanh::LeanObject,
    mut v_toApplicative_1621_: *mut leanh::LeanObject,
    mut v_inst_1622_: *mut leanh::LeanObject,
    mut v___x_1623_: *mut leanh::LeanObject,
    mut v___x_1624_: *mut leanh::LeanObject,
    mut v_t_1625_: *mut leanh::LeanObject,
    mut v_toBind_1626_: *mut leanh::LeanObject,
    mut v___x_1627_: u8,
    mut v_e_1628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getRef_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getRef_1629_ = leanh::lean_ctor_get(v_inst_1620_, 0);
    leanh::lean_inc(v_getRef_1629_);
    leanh::lean_dec_ref(v_inst_1620_);
    v_toPure_1630_ = leanh::lean_ctor_get(v_toApplicative_1621_, 1);
    leanh::lean_inc_n(v_toPure_1630_, 2);
    leanh::lean_dec_ref(v_toApplicative_1621_);
    leanh::lean_inc_n(v_toBind_1626_, 2);
    v___f_1631_ = leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__12 as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_1631_, 0, v_inst_1622_);
    leanh::lean_closure_set(v___f_1631_, 1, v___x_1623_);
    leanh::lean_closure_set(v___f_1631_, 2, v___x_1624_);
    leanh::lean_closure_set(v___f_1631_, 3, v_t_1625_);
    leanh::lean_closure_set(v___f_1631_, 4, v_e_1628_);
    leanh::lean_closure_set(v___f_1631_, 5, v_toPure_1630_);
    leanh::lean_closure_set(v___f_1631_, 6, v_toBind_1626_);
    v___x_1632_ = leanh::lean_box((v___x_1627_) as usize);
    v___f_1633_ = leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1633_, 0, v___x_1632_);
    leanh::lean_closure_set(v___f_1633_, 1, v_toPure_1630_);
    v___x_1634_ = leanh::lean_apply_4(
        v_toBind_1626_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRef_1629_,
        v___f_1633_,
    );
    v___x_1635_ = leanh::lean_apply_4(
        v_toBind_1626_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1634_,
        v___f_1631_,
    );
    return v___x_1635_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__13___boxed(
    mut v_inst_1636_: *mut leanh::LeanObject,
    mut v_toApplicative_1637_: *mut leanh::LeanObject,
    mut v_inst_1638_: *mut leanh::LeanObject,
    mut v___x_1639_: *mut leanh::LeanObject,
    mut v___x_1640_: *mut leanh::LeanObject,
    mut v_t_1641_: *mut leanh::LeanObject,
    mut v_toBind_1642_: *mut leanh::LeanObject,
    mut v___x_1643_: *mut leanh::LeanObject,
    mut v_e_1644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10216__boxed_1645_: u8 = 0;
    let mut v_res_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10216__boxed_1645_ = (leanh::lean_unbox(v___x_1643_) as u8);
    v_res_1646_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__13(
        v_inst_1636_,
        v_toApplicative_1637_,
        v_inst_1638_,
        v___x_1639_,
        v___x_1640_,
        v_t_1641_,
        v_toBind_1642_,
        v___x_10216__boxed_1645_,
        v_e_1644_,
    );
    return v_res_1646_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__28(
    mut v_info_1647_: *mut leanh::LeanObject,
    mut v___x_1648_: *mut leanh::LeanObject,
    mut v_scp_1649_: *mut leanh::LeanObject,
    mut v___x_1650_: *mut leanh::LeanObject,
    mut v___x_1651_: *mut leanh::LeanObject,
    mut v___x_1652_: *mut leanh::LeanObject,
    mut v___x_1653_: *mut leanh::LeanObject,
    mut v___x_1654_: *mut leanh::LeanObject,
    mut v___x_1655_: *mut leanh::LeanObject,
    mut v___x_1656_: *mut leanh::LeanObject,
    mut v_____do__lift_1657_: *mut leanh::LeanObject,
    mut v_toPure_1658_: *mut leanh::LeanObject,
    mut v_quotCtx_1659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1660_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15;
    leanh::lean_inc_n(v_info_1647_, 5);
    v___x_1661_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1661_, 0, v_info_1647_);
    leanh::lean_ctor_set(v___x_1661_, 1, v___x_1660_);
    v___x_1662_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17_once), _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17);
    v___x_1663_ = l_Lean_addMacroScope(v_quotCtx_1659_, v___x_1648_, v_scp_1649_);
    v___x_1664_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__0;
    v___x_1665_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__1;
    v___x_1666_ = l_Lean_Name_mkStr4(v___x_1650_, v___x_1651_, v___x_1664_, v___x_1665_);
    v___x_1667_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1667_, 0, v___x_1666_);
    v___x_1668_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20;
    leanh::lean_inc_ref_n(v___x_1652_, 3);
    v___x_1669_ = l_Lean_Name_mkStr2(v___x_1652_, v___x_1668_);
    v___x_1670_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1670_, 0, v___x_1669_);
    v___x_1671_ = l_Lean_Name_mkStr2(v___x_1652_, v___x_1653_);
    v___x_1672_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1672_, 0, v___x_1671_);
    v___x_1673_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25;
    v___x_1674_ = l_Lean_Name_mkStr2(v___x_1652_, v___x_1673_);
    v___x_1675_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1675_, 0, v___x_1674_);
    v___x_1676_ = l_Lean_Name_mkStr1(v___x_1652_);
    v___x_1677_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1677_, 0, v___x_1676_);
    v___x_1678_ = leanh::lean_box(0);
    v___x_1679_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1679_, 0, v___x_1677_);
    leanh::lean_ctor_set(v___x_1679_, 1, v___x_1678_);
    v___x_1680_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1680_, 0, v___x_1675_);
    leanh::lean_ctor_set(v___x_1680_, 1, v___x_1679_);
    v___x_1681_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1681_, 0, v___x_1672_);
    leanh::lean_ctor_set(v___x_1681_, 1, v___x_1680_);
    v___x_1682_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1682_, 0, v___x_1670_);
    leanh::lean_ctor_set(v___x_1682_, 1, v___x_1681_);
    v___x_1683_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1683_, 0, v___x_1667_);
    leanh::lean_ctor_set(v___x_1683_, 1, v___x_1682_);
    v___x_1684_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1684_, 0, v_info_1647_);
    leanh::lean_ctor_set(v___x_1684_, 1, v___x_1662_);
    leanh::lean_ctor_set(v___x_1684_, 2, v___x_1663_);
    leanh::lean_ctor_set(v___x_1684_, 3, v___x_1683_);
    v___x_1685_ = l_Lean_Syntax_node1(v_info_1647_, v___x_1654_, v___x_1684_);
    v___x_1686_ = l_Lean_Syntax_node2(v_info_1647_, v___x_1655_, v___x_1661_, v___x_1685_);
    v___x_1687_ = l_Std_Do_termSpred_x28___x29___closed__12;
    v___x_1688_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1688_, 0, v_info_1647_);
    leanh::lean_ctor_set(v___x_1688_, 1, v___x_1687_);
    v___x_1689_ = l_Lean_Syntax_node3(
        v_info_1647_,
        v___x_1656_,
        v___x_1686_,
        v_____do__lift_1657_,
        v___x_1688_,
    );
    v___x_1690_ =
        leanh::lean_apply_2(v_toPure_1658_, leanh::lean_box(0), v___x_1689_);
    return v___x_1690_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__14(
    mut v_info_1691_: *mut leanh::LeanObject,
    mut v___x_1692_: *mut leanh::LeanObject,
    mut v___x_1693_: *mut leanh::LeanObject,
    mut v___x_1694_: *mut leanh::LeanObject,
    mut v___x_1695_: *mut leanh::LeanObject,
    mut v___x_1696_: *mut leanh::LeanObject,
    mut v___x_1697_: *mut leanh::LeanObject,
    mut v___x_1698_: *mut leanh::LeanObject,
    mut v___x_1699_: *mut leanh::LeanObject,
    mut v_____do__lift_1700_: *mut leanh::LeanObject,
    mut v_toPure_1701_: *mut leanh::LeanObject,
    mut v_toBind_1702_: *mut leanh::LeanObject,
    mut v_getContext_1703_: *mut leanh::LeanObject,
    mut v_scp_1704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1705_ = leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__28 as *mut core::ffi::c_void,
        13,
        12,
    );
    leanh::lean_closure_set(v___f_1705_, 0, v_info_1691_);
    leanh::lean_closure_set(v___f_1705_, 1, v___x_1692_);
    leanh::lean_closure_set(v___f_1705_, 2, v_scp_1704_);
    leanh::lean_closure_set(v___f_1705_, 3, v___x_1693_);
    leanh::lean_closure_set(v___f_1705_, 4, v___x_1694_);
    leanh::lean_closure_set(v___f_1705_, 5, v___x_1695_);
    leanh::lean_closure_set(v___f_1705_, 6, v___x_1696_);
    leanh::lean_closure_set(v___f_1705_, 7, v___x_1697_);
    leanh::lean_closure_set(v___f_1705_, 8, v___x_1698_);
    leanh::lean_closure_set(v___f_1705_, 9, v___x_1699_);
    leanh::lean_closure_set(v___f_1705_, 10, v_____do__lift_1700_);
    leanh::lean_closure_set(v___f_1705_, 11, v_toPure_1701_);
    v___x_1706_ = leanh::lean_apply_4(
        v_toBind_1702_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getContext_1703_,
        v___f_1705_,
    );
    return v___x_1706_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__16(
    mut v_inst_1707_: *mut leanh::LeanObject,
    mut v___x_1708_: *mut leanh::LeanObject,
    mut v___x_1709_: *mut leanh::LeanObject,
    mut v___x_1710_: *mut leanh::LeanObject,
    mut v___x_1711_: *mut leanh::LeanObject,
    mut v___x_1712_: *mut leanh::LeanObject,
    mut v___x_1713_: *mut leanh::LeanObject,
    mut v___x_1714_: *mut leanh::LeanObject,
    mut v___x_1715_: *mut leanh::LeanObject,
    mut v_____do__lift_1716_: *mut leanh::LeanObject,
    mut v_toPure_1717_: *mut leanh::LeanObject,
    mut v_toBind_1718_: *mut leanh::LeanObject,
    mut v_info_1719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getCurrMacroScope_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getContext_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getCurrMacroScope_1720_ = leanh::lean_ctor_get(v_inst_1707_, 1);
    leanh::lean_inc(v_getCurrMacroScope_1720_);
    v_getContext_1721_ = leanh::lean_ctor_get(v_inst_1707_, 2);
    leanh::lean_inc(v_getContext_1721_);
    leanh::lean_dec_ref(v_inst_1707_);
    leanh::lean_inc(v_toBind_1718_);
    v___f_1722_ = leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__14 as *mut core::ffi::c_void,
        14,
        13,
    );
    leanh::lean_closure_set(v___f_1722_, 0, v_info_1719_);
    leanh::lean_closure_set(v___f_1722_, 1, v___x_1708_);
    leanh::lean_closure_set(v___f_1722_, 2, v___x_1709_);
    leanh::lean_closure_set(v___f_1722_, 3, v___x_1710_);
    leanh::lean_closure_set(v___f_1722_, 4, v___x_1711_);
    leanh::lean_closure_set(v___f_1722_, 5, v___x_1712_);
    leanh::lean_closure_set(v___f_1722_, 6, v___x_1713_);
    leanh::lean_closure_set(v___f_1722_, 7, v___x_1714_);
    leanh::lean_closure_set(v___f_1722_, 8, v___x_1715_);
    leanh::lean_closure_set(v___f_1722_, 9, v_____do__lift_1716_);
    leanh::lean_closure_set(v___f_1722_, 10, v_toPure_1717_);
    leanh::lean_closure_set(v___f_1722_, 11, v_toBind_1718_);
    leanh::lean_closure_set(v___f_1722_, 12, v_getContext_1721_);
    v___x_1723_ = leanh::lean_apply_4(
        v_toBind_1718_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getCurrMacroScope_1720_,
        v___f_1722_,
    );
    return v___x_1723_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__18(
    mut v_inst_1724_: *mut leanh::LeanObject,
    mut v_toApplicative_1725_: *mut leanh::LeanObject,
    mut v_inst_1726_: *mut leanh::LeanObject,
    mut v___x_1727_: *mut leanh::LeanObject,
    mut v___x_1728_: *mut leanh::LeanObject,
    mut v___x_1729_: *mut leanh::LeanObject,
    mut v___x_1730_: *mut leanh::LeanObject,
    mut v___x_1731_: *mut leanh::LeanObject,
    mut v___x_1732_: *mut leanh::LeanObject,
    mut v___x_1733_: *mut leanh::LeanObject,
    mut v___x_1734_: *mut leanh::LeanObject,
    mut v_toBind_1735_: *mut leanh::LeanObject,
    mut v___x_1736_: u8,
    mut v_____do__lift_1737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getRef_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getRef_1738_ = leanh::lean_ctor_get(v_inst_1724_, 0);
    leanh::lean_inc(v_getRef_1738_);
    leanh::lean_dec_ref(v_inst_1724_);
    v_toPure_1739_ = leanh::lean_ctor_get(v_toApplicative_1725_, 1);
    leanh::lean_inc_n(v_toPure_1739_, 2);
    leanh::lean_dec_ref(v_toApplicative_1725_);
    leanh::lean_inc_n(v_toBind_1735_, 2);
    v___f_1740_ = leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__16 as *mut core::ffi::c_void,
        13,
        12,
    );
    leanh::lean_closure_set(v___f_1740_, 0, v_inst_1726_);
    leanh::lean_closure_set(v___f_1740_, 1, v___x_1727_);
    leanh::lean_closure_set(v___f_1740_, 2, v___x_1728_);
    leanh::lean_closure_set(v___f_1740_, 3, v___x_1729_);
    leanh::lean_closure_set(v___f_1740_, 4, v___x_1730_);
    leanh::lean_closure_set(v___f_1740_, 5, v___x_1731_);
    leanh::lean_closure_set(v___f_1740_, 6, v___x_1732_);
    leanh::lean_closure_set(v___f_1740_, 7, v___x_1733_);
    leanh::lean_closure_set(v___f_1740_, 8, v___x_1734_);
    leanh::lean_closure_set(v___f_1740_, 9, v_____do__lift_1737_);
    leanh::lean_closure_set(v___f_1740_, 10, v_toPure_1739_);
    leanh::lean_closure_set(v___f_1740_, 11, v_toBind_1735_);
    v___x_1741_ = leanh::lean_box((v___x_1736_) as usize);
    v___f_1742_ = leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1742_, 0, v___x_1741_);
    leanh::lean_closure_set(v___f_1742_, 1, v_toPure_1739_);
    v___x_1743_ = leanh::lean_apply_4(
        v_toBind_1735_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRef_1738_,
        v___f_1742_,
    );
    v___x_1744_ = leanh::lean_apply_4(
        v_toBind_1735_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1743_,
        v___f_1740_,
    );
    return v___x_1744_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__18___boxed(
    mut v_inst_1745_: *mut leanh::LeanObject,
    mut v_toApplicative_1746_: *mut leanh::LeanObject,
    mut v_inst_1747_: *mut leanh::LeanObject,
    mut v___x_1748_: *mut leanh::LeanObject,
    mut v___x_1749_: *mut leanh::LeanObject,
    mut v___x_1750_: *mut leanh::LeanObject,
    mut v___x_1751_: *mut leanh::LeanObject,
    mut v___x_1752_: *mut leanh::LeanObject,
    mut v___x_1753_: *mut leanh::LeanObject,
    mut v___x_1754_: *mut leanh::LeanObject,
    mut v___x_1755_: *mut leanh::LeanObject,
    mut v_toBind_1756_: *mut leanh::LeanObject,
    mut v___x_1757_: *mut leanh::LeanObject,
    mut v_____do__lift_1758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10395__boxed_1759_: u8 = 0;
    let mut v_res_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10395__boxed_1759_ = (leanh::lean_unbox(v___x_1757_) as u8);
    v_res_1760_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__18(
        v_inst_1745_,
        v_toApplicative_1746_,
        v_inst_1747_,
        v___x_1748_,
        v___x_1749_,
        v___x_1750_,
        v___x_1751_,
        v___x_1752_,
        v___x_1753_,
        v___x_1754_,
        v___x_1755_,
        v_toBind_1756_,
        v___x_10395__boxed_1759_,
        v_____do__lift_1758_,
    );
    return v_res_1760_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__22(
    mut v_toPure_1761_: *mut leanh::LeanObject,
    mut v_____do__lift_1762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1763_ = 0;
    v___x_1764_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1762_, v___x_1763_);
    v___x_1765_ =
        leanh::lean_apply_2(v_toPure_1761_, leanh::lean_box(0), v___x_1764_);
    return v___x_1765_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__22___boxed(
    mut v_toPure_1766_: *mut leanh::LeanObject,
    mut v_____do__lift_1767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1768_ =
        l_Std_Do_SPred_Notation_unpack___redArg___lam__22(v_toPure_1766_, v_____do__lift_1767_);
    leanh::lean_dec(v_____do__lift_1767_);
    return v_res_1768_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__17(
    mut v_toPure_1769_: *mut leanh::LeanObject,
    mut v___x_1770_: *mut leanh::LeanObject,
    mut v_quotCtx_1771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1772_ =
        leanh::lean_apply_2(v_toPure_1769_, leanh::lean_box(0), v___x_1770_);
    return v___x_1772_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__17___boxed(
    mut v_toPure_1773_: *mut leanh::LeanObject,
    mut v___x_1774_: *mut leanh::LeanObject,
    mut v_quotCtx_1775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1776_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__17(
        v_toPure_1773_,
        v___x_1774_,
        v_quotCtx_1775_,
    );
    leanh::lean_dec(v_quotCtx_1775_);
    return v_res_1776_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__11___boxed(
    mut v_inst_1777_: *mut leanh::LeanObject,
    mut v_toApplicative_1778_: *mut leanh::LeanObject,
    mut v_inst_1779_: *mut leanh::LeanObject,
    mut v___x_1780_: *mut leanh::LeanObject,
    mut v___x_1781_: *mut leanh::LeanObject,
    mut v_toBind_1782_: *mut leanh::LeanObject,
    mut v___x_1783_: *mut leanh::LeanObject,
    mut v_inst_1784_: *mut leanh::LeanObject,
    mut v_e_1785_: *mut leanh::LeanObject,
    mut v_t_1786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10507__boxed_1787_: u8 = 0;
    let mut v_res_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10507__boxed_1787_ = (leanh::lean_unbox(v___x_1783_) as u8);
    v_res_1788_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__11(
        v_inst_1777_,
        v_toApplicative_1778_,
        v_inst_1779_,
        v___x_1780_,
        v___x_1781_,
        v_toBind_1782_,
        v___x_10507__boxed_1787_,
        v_inst_1784_,
        v_e_1785_,
        v_t_1786_,
    );
    return v_res_1788_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg(
    mut v_inst_1789_: *mut leanh::LeanObject,
    mut v_inst_1790_: *mut leanh::LeanObject,
    mut v_inst_1791_: *mut leanh::LeanObject,
    mut v_x_1792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: u8 = 0;
    v___x_1793_ = l_Std_Do_termSpred_x28___x29___closed__0;
    v___x_1794_ = l_Std_Do_termSpred_x28___x29___closed__1;
    v___x_1795_ = l_Std_Do_termSpred_x28___x29___closed__3;
    leanh::lean_inc(v_x_1792_);
    v___x_1796_ = l_Lean_Syntax_isOfKind(v_x_1792_, v___x_1795_);
    if v___x_1796_ == 0 {
        let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1800_: u8 = 0;
        v___x_1797_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0;
        v___x_1798_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1;
        v___x_1799_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4;
        leanh::lean_inc(v_x_1792_);
        v___x_1800_ = l_Lean_Syntax_isOfKind(v_x_1792_, v___x_1799_);
        if v___x_1800_ == 0 {
            let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1802_: u8 = 0;
            v___x_1801_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__8;
            leanh::lean_inc(v_x_1792_);
            v___x_1802_ = l_Lean_Syntax_isOfKind(v_x_1792_, v___x_1801_);
            if v___x_1802_ == 0 {
                let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1805_: u8 = 0;
                v___x_1803_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__5;
                v___x_1804_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6;
                leanh::lean_inc(v_x_1792_);
                v___x_1805_ = l_Lean_Syntax_isOfKind(v_x_1792_, v___x_1804_);
                if v___x_1805_ == 0 {
                    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1807_: u8 = 0;
                    v___x_1806_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10;
                    leanh::lean_inc(v_x_1792_);
                    v___x_1807_ = l_Lean_Syntax_isOfKind(v_x_1792_, v___x_1806_);
                    if v___x_1807_ == 0 {
                        let mut v_toApplicative_1808_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_toBind_1809_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_getRef_1810_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_toPure_1811_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v___f_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___f_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___f_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___f_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_toApplicative_1808_ = leanh::lean_ctor_get(v_inst_1789_, 0);
                        leanh::lean_inc_ref(v_toApplicative_1808_);
                        v_toBind_1809_ = leanh::lean_ctor_get(v_inst_1789_, 1);
                        leanh::lean_inc_n(v_toBind_1809_, 4);
                        leanh::lean_dec_ref(v_inst_1789_);
                        v_getRef_1810_ = leanh::lean_ctor_get(v_inst_1790_, 0);
                        leanh::lean_inc(v_getRef_1810_);
                        leanh::lean_dec_ref(v_inst_1790_);
                        v_toPure_1811_ = leanh::lean_ctor_get(v_toApplicative_1808_, 1);
                        leanh::lean_inc_n(v_toPure_1811_, 2);
                        leanh::lean_dec_ref(v_toApplicative_1808_);
                        v___f_1812_ = leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        leanh::lean_closure_set(v___f_1812_, 0, v_toPure_1811_);
                        leanh::lean_closure_set(v___f_1812_, 1, v_x_1792_);
                        leanh::lean_inc_ref(v_inst_1791_);
                        v___f_1813_ = leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        leanh::lean_closure_set(v___f_1813_, 0, v_inst_1791_);
                        leanh::lean_closure_set(v___f_1813_, 1, v_toBind_1809_);
                        leanh::lean_closure_set(v___f_1813_, 2, v___f_1812_);
                        v___f_1814_ = leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        leanh::lean_closure_set(v___f_1814_, 0, v_inst_1791_);
                        leanh::lean_closure_set(v___f_1814_, 1, v_toBind_1809_);
                        leanh::lean_closure_set(v___f_1814_, 2, v___f_1813_);
                        v___x_1815_ = leanh::lean_box((v___x_1807_) as usize);
                        v___f_1816_ = leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        leanh::lean_closure_set(v___f_1816_, 0, v___x_1815_);
                        leanh::lean_closure_set(v___f_1816_, 1, v_toPure_1811_);
                        v___x_1817_ = leanh::lean_apply_4(
                            v_toBind_1809_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v_getRef_1810_,
                            v___f_1816_,
                        );
                        v___x_1818_ = leanh::lean_apply_4(
                            v_toBind_1809_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_1817_,
                            v___f_1814_,
                        );
                        return v___x_1818_;
                    } else {
                        let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1822_: u8 = 0;
                        v___x_1819_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1820_ = l_Lean_Syntax_getArg(v_x_1792_, v___x_1819_);
                        v___x_1821_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12;
                        leanh::lean_inc(v___x_1820_);
                        v___x_1822_ = l_Lean_Syntax_isOfKind(v___x_1820_, v___x_1821_);
                        if v___x_1822_ == 0 {
                            let mut v_toApplicative_1823_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_toBind_1824_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_getRef_1825_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_toPure_1826_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___f_1827_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___f_1828_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___f_1829_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1830_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___f_1831_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1832_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1833_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            leanh::lean_dec(v___x_1820_);
                            v_toApplicative_1823_ = leanh::lean_ctor_get(v_inst_1789_, 0);
                            leanh::lean_inc_ref(v_toApplicative_1823_);
                            v_toBind_1824_ = leanh::lean_ctor_get(v_inst_1789_, 1);
                            leanh::lean_inc_n(v_toBind_1824_, 4);
                            leanh::lean_dec_ref(v_inst_1789_);
                            v_getRef_1825_ = leanh::lean_ctor_get(v_inst_1790_, 0);
                            leanh::lean_inc(v_getRef_1825_);
                            leanh::lean_dec_ref(v_inst_1790_);
                            v_toPure_1826_ = leanh::lean_ctor_get(v_toApplicative_1823_, 1);
                            leanh::lean_inc_n(v_toPure_1826_, 2);
                            leanh::lean_dec_ref(v_toApplicative_1823_);
                            v___f_1827_ = leanh::lean_alloc_closure(
                                l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                3,
                                2,
                            );
                            leanh::lean_closure_set(v___f_1827_, 0, v_toPure_1826_);
                            leanh::lean_closure_set(v___f_1827_, 1, v_x_1792_);
                            leanh::lean_inc_ref(v_inst_1791_);
                            v___f_1828_ = leanh::lean_alloc_closure(
                                l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed
                                    as *mut core::ffi::c_void,
                                4,
                                3,
                            );
                            leanh::lean_closure_set(v___f_1828_, 0, v_inst_1791_);
                            leanh::lean_closure_set(v___f_1828_, 1, v_toBind_1824_);
                            leanh::lean_closure_set(v___f_1828_, 2, v___f_1827_);
                            v___f_1829_ = leanh::lean_alloc_closure(
                                l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed
                                    as *mut core::ffi::c_void,
                                4,
                                3,
                            );
                            leanh::lean_closure_set(v___f_1829_, 0, v_inst_1791_);
                            leanh::lean_closure_set(v___f_1829_, 1, v_toBind_1824_);
                            leanh::lean_closure_set(v___f_1829_, 2, v___f_1828_);
                            v___x_1830_ = leanh::lean_box((v___x_1822_) as usize);
                            v___f_1831_ = leanh::lean_alloc_closure(
                                l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed
                                    as *mut core::ffi::c_void,
                                3,
                                2,
                            );
                            leanh::lean_closure_set(v___f_1831_, 0, v___x_1830_);
                            leanh::lean_closure_set(v___f_1831_, 1, v_toPure_1826_);
                            v___x_1832_ = leanh::lean_apply_4(
                                v_toBind_1824_,
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v_getRef_1825_,
                                v___f_1831_,
                            );
                            v___x_1833_ = leanh::lean_apply_4(
                                v_toBind_1824_,
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_1832_,
                                v___f_1829_,
                            );
                            return v___x_1833_;
                        } else {
                            let mut v___x_1834_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1835_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1836_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1837_: u8 = 0;
                            v___x_1834_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1835_ = l_Lean_Syntax_getArg(v___x_1820_, v___x_1834_);
                            leanh::lean_dec(v___x_1820_);
                            v___x_1836_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14;
                            leanh::lean_inc(v___x_1835_);
                            v___x_1837_ = l_Lean_Syntax_isOfKind(v___x_1835_, v___x_1836_);
                            if v___x_1837_ == 0 {
                                let mut v_toApplicative_1838_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v_toBind_1839_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v_getRef_1840_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v_toPure_1841_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___f_1842_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___f_1843_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___f_1844_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1845_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___f_1846_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1847_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1848_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                leanh::lean_dec(v___x_1835_);
                                v_toApplicative_1838_ =
                                    leanh::lean_ctor_get(v_inst_1789_, 0);
                                leanh::lean_inc_ref(v_toApplicative_1838_);
                                v_toBind_1839_ = leanh::lean_ctor_get(v_inst_1789_, 1);
                                leanh::lean_inc_n(v_toBind_1839_, 4);
                                leanh::lean_dec_ref(v_inst_1789_);
                                v_getRef_1840_ = leanh::lean_ctor_get(v_inst_1790_, 0);
                                leanh::lean_inc(v_getRef_1840_);
                                leanh::lean_dec_ref(v_inst_1790_);
                                v_toPure_1841_ =
                                    leanh::lean_ctor_get(v_toApplicative_1838_, 1);
                                leanh::lean_inc_n(v_toPure_1841_, 2);
                                leanh::lean_dec_ref(v_toApplicative_1838_);
                                v___f_1842_ = leanh::lean_alloc_closure(
                                    l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    3,
                                    2,
                                );
                                leanh::lean_closure_set(v___f_1842_, 0, v_toPure_1841_);
                                leanh::lean_closure_set(v___f_1842_, 1, v_x_1792_);
                                leanh::lean_inc_ref(v_inst_1791_);
                                v___f_1843_ = leanh::lean_alloc_closure(
                                    l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed
                                        as *mut core::ffi::c_void,
                                    4,
                                    3,
                                );
                                leanh::lean_closure_set(v___f_1843_, 0, v_inst_1791_);
                                leanh::lean_closure_set(v___f_1843_, 1, v_toBind_1839_);
                                leanh::lean_closure_set(v___f_1843_, 2, v___f_1842_);
                                v___f_1844_ = leanh::lean_alloc_closure(
                                    l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed
                                        as *mut core::ffi::c_void,
                                    4,
                                    3,
                                );
                                leanh::lean_closure_set(v___f_1844_, 0, v_inst_1791_);
                                leanh::lean_closure_set(v___f_1844_, 1, v_toBind_1839_);
                                leanh::lean_closure_set(v___f_1844_, 2, v___f_1843_);
                                v___x_1845_ = leanh::lean_box((v___x_1837_) as usize);
                                v___f_1846_ = leanh::lean_alloc_closure(
                                    l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed
                                        as *mut core::ffi::c_void,
                                    3,
                                    2,
                                );
                                leanh::lean_closure_set(v___f_1846_, 0, v___x_1845_);
                                leanh::lean_closure_set(v___f_1846_, 1, v_toPure_1841_);
                                v___x_1847_ = leanh::lean_apply_4(
                                    v_toBind_1839_,
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v_getRef_1840_,
                                    v___f_1846_,
                                );
                                v___x_1848_ = leanh::lean_apply_4(
                                    v_toBind_1839_,
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_1847_,
                                    v___f_1844_,
                                );
                                return v___x_1848_;
                            } else {
                                let mut v___x_1849_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1850_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1851_: u8 = 0;
                                v___x_1849_ = l_Lean_Syntax_getArg(v___x_1835_, v___x_1819_);
                                leanh::lean_dec(v___x_1835_);
                                v___x_1850_ = leanh::lean_box(0);
                                v___x_1851_ = l_Lean_Syntax_matchesIdent(v___x_1849_, v___x_1850_);
                                leanh::lean_dec(v___x_1849_);
                                if v___x_1851_ == 0 {
                                    let mut v_toApplicative_1852_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v_toBind_1853_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v_getRef_1854_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v_toPure_1855_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___f_1856_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___f_1857_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___f_1858_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1859_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___f_1860_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1861_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1862_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    v_toApplicative_1852_ =
                                        leanh::lean_ctor_get(v_inst_1789_, 0);
                                    leanh::lean_inc_ref(v_toApplicative_1852_);
                                    v_toBind_1853_ = leanh::lean_ctor_get(v_inst_1789_, 1);
                                    leanh::lean_inc_n(v_toBind_1853_, 4);
                                    leanh::lean_dec_ref(v_inst_1789_);
                                    v_getRef_1854_ = leanh::lean_ctor_get(v_inst_1790_, 0);
                                    leanh::lean_inc(v_getRef_1854_);
                                    leanh::lean_dec_ref(v_inst_1790_);
                                    v_toPure_1855_ =
                                        leanh::lean_ctor_get(v_toApplicative_1852_, 1);
                                    leanh::lean_inc_n(v_toPure_1855_, 2);
                                    leanh::lean_dec_ref(v_toApplicative_1852_);
                                    v___f_1856_ = leanh::lean_alloc_closure(
                                        l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed
                                            as *mut core::ffi::c_void,
                                        3,
                                        2,
                                    );
                                    leanh::lean_closure_set(v___f_1856_, 0, v_toPure_1855_);
                                    leanh::lean_closure_set(v___f_1856_, 1, v_x_1792_);
                                    leanh::lean_inc_ref(v_inst_1791_);
                                    v___f_1857_ = leanh::lean_alloc_closure(
                                        l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed
                                            as *mut core::ffi::c_void,
                                        4,
                                        3,
                                    );
                                    leanh::lean_closure_set(v___f_1857_, 0, v_inst_1791_);
                                    leanh::lean_closure_set(v___f_1857_, 1, v_toBind_1853_);
                                    leanh::lean_closure_set(v___f_1857_, 2, v___f_1856_);
                                    v___f_1858_ = leanh::lean_alloc_closure(
                                        l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed
                                            as *mut core::ffi::c_void,
                                        4,
                                        3,
                                    );
                                    leanh::lean_closure_set(v___f_1858_, 0, v_inst_1791_);
                                    leanh::lean_closure_set(v___f_1858_, 1, v_toBind_1853_);
                                    leanh::lean_closure_set(v___f_1858_, 2, v___f_1857_);
                                    v___x_1859_ = leanh::lean_box((v___x_1851_) as usize);
                                    v___f_1860_ = leanh::lean_alloc_closure(
                                        l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed
                                            as *mut core::ffi::c_void,
                                        3,
                                        2,
                                    );
                                    leanh::lean_closure_set(v___f_1860_, 0, v___x_1859_);
                                    leanh::lean_closure_set(v___f_1860_, 1, v_toPure_1855_);
                                    v___x_1861_ = leanh::lean_apply_4(
                                        v_toBind_1853_,
                                        leanh::lean_box(0),
                                        leanh::lean_box(0),
                                        v_getRef_1854_,
                                        v___f_1860_,
                                    );
                                    v___x_1862_ = leanh::lean_apply_4(
                                        v_toBind_1853_,
                                        leanh::lean_box(0),
                                        leanh::lean_box(0),
                                        v___x_1861_,
                                        v___f_1858_,
                                    );
                                    return v___x_1862_;
                                } else {
                                    let mut v___x_1863_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1864_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1865_: u8 = 0;
                                    v___x_1863_ = leanh::lean_unsigned_to_nat(3);
                                    v___x_1864_ = l_Lean_Syntax_getArg(v_x_1792_, v___x_1863_);
                                    leanh::lean_inc(v___x_1864_);
                                    v___x_1865_ =
                                        l_Lean_Syntax_matchesNull(v___x_1864_, v___x_1834_);
                                    if v___x_1865_ == 0 {
                                        let mut v_toApplicative_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
                                        let mut v_toBind_1867_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v_getRef_1868_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v_toPure_1869_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___f_1870_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___f_1871_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___f_1872_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1873_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___f_1874_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1875_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1876_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        leanh::lean_dec(v___x_1864_);
                                        v_toApplicative_1866_ =
                                            leanh::lean_ctor_get(v_inst_1789_, 0);
                                        leanh::lean_inc_ref(v_toApplicative_1866_);
                                        v_toBind_1867_ =
                                            leanh::lean_ctor_get(v_inst_1789_, 1);
                                        leanh::lean_inc_n(v_toBind_1867_, 4);
                                        leanh::lean_dec_ref(v_inst_1789_);
                                        v_getRef_1868_ =
                                            leanh::lean_ctor_get(v_inst_1790_, 0);
                                        leanh::lean_inc(v_getRef_1868_);
                                        leanh::lean_dec_ref(v_inst_1790_);
                                        v_toPure_1869_ =
                                            leanh::lean_ctor_get(v_toApplicative_1866_, 1);
                                        leanh::lean_inc_n(v_toPure_1869_, 2);
                                        leanh::lean_dec_ref(v_toApplicative_1866_);
                                        v___f_1870_ = leanh::lean_alloc_closure(
                                            l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed
                                                as *mut core::ffi::c_void,
                                            3,
                                            2,
                                        );
                                        leanh::lean_closure_set(
                                            v___f_1870_,
                                            0,
                                            v_toPure_1869_,
                                        );
                                        leanh::lean_closure_set(v___f_1870_, 1, v_x_1792_);
                                        leanh::lean_inc_ref(v_inst_1791_);
                                        v___f_1871_ = leanh::lean_alloc_closure(
                                            l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed
                                                as *mut core::ffi::c_void,
                                            4,
                                            3,
                                        );
                                        leanh::lean_closure_set(
                                            v___f_1871_,
                                            0,
                                            v_inst_1791_,
                                        );
                                        leanh::lean_closure_set(
                                            v___f_1871_,
                                            1,
                                            v_toBind_1867_,
                                        );
                                        leanh::lean_closure_set(v___f_1871_, 2, v___f_1870_);
                                        v___f_1872_ = leanh::lean_alloc_closure(
                                            l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed
                                                as *mut core::ffi::c_void,
                                            4,
                                            3,
                                        );
                                        leanh::lean_closure_set(
                                            v___f_1872_,
                                            0,
                                            v_inst_1791_,
                                        );
                                        leanh::lean_closure_set(
                                            v___f_1872_,
                                            1,
                                            v_toBind_1867_,
                                        );
                                        leanh::lean_closure_set(v___f_1872_, 2, v___f_1871_);
                                        v___x_1873_ =
                                            leanh::lean_box((v___x_1865_) as usize);
                                        v___f_1874_ = leanh::lean_alloc_closure(
                                            l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed
                                                as *mut core::ffi::c_void,
                                            3,
                                            2,
                                        );
                                        leanh::lean_closure_set(v___f_1874_, 0, v___x_1873_);
                                        leanh::lean_closure_set(
                                            v___f_1874_,
                                            1,
                                            v_toPure_1869_,
                                        );
                                        v___x_1875_ = leanh::lean_apply_4(
                                            v_toBind_1867_,
                                            leanh::lean_box(0),
                                            leanh::lean_box(0),
                                            v_getRef_1868_,
                                            v___f_1874_,
                                        );
                                        v___x_1876_ = leanh::lean_apply_4(
                                            v_toBind_1867_,
                                            leanh::lean_box(0),
                                            leanh::lean_box(0),
                                            v___x_1875_,
                                            v___f_1872_,
                                        );
                                        return v___x_1876_;
                                    } else {
                                        let mut v_toApplicative_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
                                        let mut v_toBind_1878_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v_P_1879_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1880_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1881_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___f_1882_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1883_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1884_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        v_toApplicative_1877_ =
                                            leanh::lean_ctor_get(v_inst_1789_, 0);
                                        v_toBind_1878_ =
                                            leanh::lean_ctor_get(v_inst_1789_, 1);
                                        leanh::lean_inc_n(v_toBind_1878_, 2);
                                        v_P_1879_ = l_Lean_Syntax_getArg(v_x_1792_, v___x_1834_);
                                        leanh::lean_dec(v_x_1792_);
                                        v___x_1880_ =
                                            l_Lean_Syntax_getArg(v___x_1864_, v___x_1819_);
                                        leanh::lean_dec(v___x_1864_);
                                        v___x_1881_ =
                                            leanh::lean_box((v___x_1805_) as usize);
                                        leanh::lean_inc_ref(v_inst_1791_);
                                        leanh::lean_inc_ref(v_toApplicative_1877_);
                                        leanh::lean_inc_ref(v_inst_1790_);
                                        v___f_1882_ = leanh::lean_alloc_closure(
                                            l_Std_Do_SPred_Notation_unpack___redArg___lam__7___boxed
                                                as *mut core::ffi::c_void,
                                            15,
                                            14,
                                        );
                                        leanh::lean_closure_set(
                                            v___f_1882_,
                                            0,
                                            v_inst_1790_,
                                        );
                                        leanh::lean_closure_set(
                                            v___f_1882_,
                                            1,
                                            v_toApplicative_1877_,
                                        );
                                        leanh::lean_closure_set(
                                            v___f_1882_,
                                            2,
                                            v_inst_1791_,
                                        );
                                        leanh::lean_closure_set(v___f_1882_, 3, v___x_1850_);
                                        leanh::lean_closure_set(v___f_1882_, 4, v___x_1793_);
                                        leanh::lean_closure_set(v___f_1882_, 5, v___x_1794_);
                                        leanh::lean_closure_set(v___f_1882_, 6, v___x_1797_);
                                        leanh::lean_closure_set(v___f_1882_, 7, v___x_1798_);
                                        leanh::lean_closure_set(v___f_1882_, 8, v___x_1836_);
                                        leanh::lean_closure_set(v___f_1882_, 9, v___x_1821_);
                                        leanh::lean_closure_set(
                                            v___f_1882_,
                                            10,
                                            v___x_1880_,
                                        );
                                        leanh::lean_closure_set(
                                            v___f_1882_,
                                            11,
                                            v___x_1806_,
                                        );
                                        leanh::lean_closure_set(
                                            v___f_1882_,
                                            12,
                                            v_toBind_1878_,
                                        );
                                        leanh::lean_closure_set(
                                            v___f_1882_,
                                            13,
                                            v___x_1881_,
                                        );
                                        v___x_1883_ = l_Std_Do_SPred_Notation_unpack___redArg(
                                            v_inst_1789_,
                                            v_inst_1790_,
                                            v_inst_1791_,
                                            v_P_1879_,
                                        );
                                        v___x_1884_ = leanh::lean_apply_4(
                                            v_toBind_1878_,
                                            leanh::lean_box(0),
                                            leanh::lean_box(0),
                                            v___x_1883_,
                                            v___f_1882_,
                                        );
                                        return v___x_1884_;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1888_: u8 = 0;
                    v___x_1885_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1886_ = l_Lean_Syntax_getArg(v_x_1792_, v___x_1885_);
                    v___x_1887_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42;
                    leanh::lean_inc(v___x_1886_);
                    v___x_1888_ = l_Lean_Syntax_isOfKind(v___x_1886_, v___x_1887_);
                    if v___x_1888_ == 0 {
                        let mut v_toApplicative_1889_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_toBind_1890_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_getRef_1891_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_toPure_1892_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v___f_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___f_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___f_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___f_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
                        leanh::lean_dec(v___x_1886_);
                        v_toApplicative_1889_ = leanh::lean_ctor_get(v_inst_1789_, 0);
                        leanh::lean_inc_ref(v_toApplicative_1889_);
                        v_toBind_1890_ = leanh::lean_ctor_get(v_inst_1789_, 1);
                        leanh::lean_inc_n(v_toBind_1890_, 4);
                        leanh::lean_dec_ref(v_inst_1789_);
                        v_getRef_1891_ = leanh::lean_ctor_get(v_inst_1790_, 0);
                        leanh::lean_inc(v_getRef_1891_);
                        leanh::lean_dec_ref(v_inst_1790_);
                        v_toPure_1892_ = leanh::lean_ctor_get(v_toApplicative_1889_, 1);
                        leanh::lean_inc_n(v_toPure_1892_, 2);
                        leanh::lean_dec_ref(v_toApplicative_1889_);
                        v___f_1893_ = leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        leanh::lean_closure_set(v___f_1893_, 0, v_toPure_1892_);
                        leanh::lean_closure_set(v___f_1893_, 1, v_x_1792_);
                        leanh::lean_inc_ref(v_inst_1791_);
                        v___f_1894_ = leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        leanh::lean_closure_set(v___f_1894_, 0, v_inst_1791_);
                        leanh::lean_closure_set(v___f_1894_, 1, v_toBind_1890_);
                        leanh::lean_closure_set(v___f_1894_, 2, v___f_1893_);
                        v___f_1895_ = leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        leanh::lean_closure_set(v___f_1895_, 0, v_inst_1791_);
                        leanh::lean_closure_set(v___f_1895_, 1, v_toBind_1890_);
                        leanh::lean_closure_set(v___f_1895_, 2, v___f_1894_);
                        v___x_1896_ = leanh::lean_box((v___x_1888_) as usize);
                        v___f_1897_ = leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        leanh::lean_closure_set(v___f_1897_, 0, v___x_1896_);
                        leanh::lean_closure_set(v___f_1897_, 1, v_toPure_1892_);
                        v___x_1898_ = leanh::lean_apply_4(
                            v_toBind_1890_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v_getRef_1891_,
                            v___f_1897_,
                        );
                        v___x_1899_ = leanh::lean_apply_4(
                            v_toBind_1890_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_1898_,
                            v___f_1895_,
                        );
                        return v___x_1899_;
                    } else {
                        let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1902_: u8 = 0;
                        v___x_1900_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1901_ = l_Lean_Syntax_getArg(v___x_1886_, v___x_1885_);
                        v___x_1902_ = l_Lean_Syntax_matchesNull(v___x_1901_, v___x_1900_);
                        if v___x_1902_ == 0 {
                            let mut v_toApplicative_1903_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_toBind_1904_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_getRef_1905_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_toPure_1906_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___f_1907_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___f_1908_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___f_1909_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1910_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___f_1911_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1912_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1913_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            leanh::lean_dec(v___x_1886_);
                            v_toApplicative_1903_ = leanh::lean_ctor_get(v_inst_1789_, 0);
                            leanh::lean_inc_ref(v_toApplicative_1903_);
                            v_toBind_1904_ = leanh::lean_ctor_get(v_inst_1789_, 1);
                            leanh::lean_inc_n(v_toBind_1904_, 4);
                            leanh::lean_dec_ref(v_inst_1789_);
                            v_getRef_1905_ = leanh::lean_ctor_get(v_inst_1790_, 0);
                            leanh::lean_inc(v_getRef_1905_);
                            leanh::lean_dec_ref(v_inst_1790_);
                            v_toPure_1906_ = leanh::lean_ctor_get(v_toApplicative_1903_, 1);
                            leanh::lean_inc_n(v_toPure_1906_, 2);
                            leanh::lean_dec_ref(v_toApplicative_1903_);
                            v___f_1907_ = leanh::lean_alloc_closure(
                                l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                3,
                                2,
                            );
                            leanh::lean_closure_set(v___f_1907_, 0, v_toPure_1906_);
                            leanh::lean_closure_set(v___f_1907_, 1, v_x_1792_);
                            leanh::lean_inc_ref(v_inst_1791_);
                            v___f_1908_ = leanh::lean_alloc_closure(
                                l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed
                                    as *mut core::ffi::c_void,
                                4,
                                3,
                            );
                            leanh::lean_closure_set(v___f_1908_, 0, v_inst_1791_);
                            leanh::lean_closure_set(v___f_1908_, 1, v_toBind_1904_);
                            leanh::lean_closure_set(v___f_1908_, 2, v___f_1907_);
                            v___f_1909_ = leanh::lean_alloc_closure(
                                l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed
                                    as *mut core::ffi::c_void,
                                4,
                                3,
                            );
                            leanh::lean_closure_set(v___f_1909_, 0, v_inst_1791_);
                            leanh::lean_closure_set(v___f_1909_, 1, v_toBind_1904_);
                            leanh::lean_closure_set(v___f_1909_, 2, v___f_1908_);
                            v___x_1910_ = leanh::lean_box((v___x_1902_) as usize);
                            v___f_1911_ = leanh::lean_alloc_closure(
                                l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed
                                    as *mut core::ffi::c_void,
                                3,
                                2,
                            );
                            leanh::lean_closure_set(v___f_1911_, 0, v___x_1910_);
                            leanh::lean_closure_set(v___f_1911_, 1, v_toPure_1906_);
                            v___x_1912_ = leanh::lean_apply_4(
                                v_toBind_1904_,
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v_getRef_1905_,
                                v___f_1911_,
                            );
                            v___x_1913_ = leanh::lean_apply_4(
                                v_toBind_1904_,
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_1912_,
                                v___f_1909_,
                            );
                            return v___x_1913_;
                        } else {
                            let mut v_toApplicative_1914_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_toBind_1915_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1916_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1917_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_b_1918_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_xs_1919_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1920_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___f_1921_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1922_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1923_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            leanh::lean_dec(v_x_1792_);
                            v_toApplicative_1914_ = leanh::lean_ctor_get(v_inst_1789_, 0);
                            v_toBind_1915_ = leanh::lean_ctor_get(v_inst_1789_, 1);
                            leanh::lean_inc_n(v_toBind_1915_, 2);
                            v___x_1916_ = l_Lean_Syntax_getArg(v___x_1886_, v___x_1900_);
                            v___x_1917_ = leanh::lean_unsigned_to_nat(3);
                            v_b_1918_ = l_Lean_Syntax_getArg(v___x_1886_, v___x_1917_);
                            leanh::lean_dec(v___x_1886_);
                            v_xs_1919_ = l_Lean_Syntax_getArgs(v___x_1916_);
                            leanh::lean_dec(v___x_1916_);
                            v___x_1920_ = leanh::lean_box((v___x_1802_) as usize);
                            leanh::lean_inc_ref(v_inst_1791_);
                            leanh::lean_inc_ref(v_toApplicative_1914_);
                            leanh::lean_inc_ref(v_inst_1790_);
                            v___f_1921_ = leanh::lean_alloc_closure(
                                l_Std_Do_SPred_Notation_unpack___redArg___lam__10___boxed
                                    as *mut core::ffi::c_void,
                                10,
                                9,
                            );
                            leanh::lean_closure_set(v___f_1921_, 0, v_inst_1790_);
                            leanh::lean_closure_set(v___f_1921_, 1, v_toApplicative_1914_);
                            leanh::lean_closure_set(v___f_1921_, 2, v_inst_1791_);
                            leanh::lean_closure_set(v___f_1921_, 3, v___x_1803_);
                            leanh::lean_closure_set(v___f_1921_, 4, v_xs_1919_);
                            leanh::lean_closure_set(v___f_1921_, 5, v___x_1887_);
                            leanh::lean_closure_set(v___f_1921_, 6, v___x_1804_);
                            leanh::lean_closure_set(v___f_1921_, 7, v_toBind_1915_);
                            leanh::lean_closure_set(v___f_1921_, 8, v___x_1920_);
                            v___x_1922_ = l_Std_Do_SPred_Notation_unpack___redArg(
                                v_inst_1789_,
                                v_inst_1790_,
                                v_inst_1791_,
                                v_b_1918_,
                            );
                            v___x_1923_ = leanh::lean_apply_4(
                                v_toBind_1915_,
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_1922_,
                                v___f_1921_,
                            );
                            return v___x_1923_;
                        }
                    }
                }
            } else {
                let mut v_toApplicative_1924_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toBind_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_t_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_e_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_toApplicative_1924_ = leanh::lean_ctor_get(v_inst_1789_, 0);
                v_toBind_1925_ = leanh::lean_ctor_get(v_inst_1789_, 1);
                leanh::lean_inc_n(v_toBind_1925_, 2);
                v___x_1926_ = leanh::lean_unsigned_to_nat(1);
                v___x_1927_ = l_Lean_Syntax_getArg(v_x_1792_, v___x_1926_);
                v___x_1928_ = leanh::lean_unsigned_to_nat(3);
                v_t_1929_ = l_Lean_Syntax_getArg(v_x_1792_, v___x_1928_);
                v___x_1930_ = leanh::lean_unsigned_to_nat(5);
                v_e_1931_ = l_Lean_Syntax_getArg(v_x_1792_, v___x_1930_);
                leanh::lean_dec(v_x_1792_);
                v___x_1932_ = leanh::lean_box((v___x_1800_) as usize);
                leanh::lean_inc_ref(v_inst_1789_);
                leanh::lean_inc_ref(v_inst_1791_);
                leanh::lean_inc_ref(v_toApplicative_1924_);
                leanh::lean_inc_ref(v_inst_1790_);
                v___f_1933_ = leanh::lean_alloc_closure(
                    l_Std_Do_SPred_Notation_unpack___redArg___lam__11___boxed
                        as *mut core::ffi::c_void,
                    10,
                    9,
                );
                leanh::lean_closure_set(v___f_1933_, 0, v_inst_1790_);
                leanh::lean_closure_set(v___f_1933_, 1, v_toApplicative_1924_);
                leanh::lean_closure_set(v___f_1933_, 2, v_inst_1791_);
                leanh::lean_closure_set(v___f_1933_, 3, v___x_1801_);
                leanh::lean_closure_set(v___f_1933_, 4, v___x_1927_);
                leanh::lean_closure_set(v___f_1933_, 5, v_toBind_1925_);
                leanh::lean_closure_set(v___f_1933_, 6, v___x_1932_);
                leanh::lean_closure_set(v___f_1933_, 7, v_inst_1789_);
                leanh::lean_closure_set(v___f_1933_, 8, v_e_1931_);
                v___x_1934_ = l_Std_Do_SPred_Notation_unpack___redArg(
                    v_inst_1789_,
                    v_inst_1790_,
                    v_inst_1791_,
                    v_t_1929_,
                );
                v___x_1935_ = leanh::lean_apply_4(
                    v_toBind_1925_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1934_,
                    v___f_1933_,
                );
                return v___x_1935_;
            }
        } else {
            let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1939_: u8 = 0;
            v___x_1936_ = leanh::lean_unsigned_to_nat(0);
            v___x_1937_ = l_Lean_Syntax_getArg(v_x_1792_, v___x_1936_);
            v___x_1938_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12;
            leanh::lean_inc(v___x_1937_);
            v___x_1939_ = l_Lean_Syntax_isOfKind(v___x_1937_, v___x_1938_);
            if v___x_1939_ == 0 {
                let mut v_toApplicative_1940_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toBind_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_getRef_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_toPure_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_1937_);
                v_toApplicative_1940_ = leanh::lean_ctor_get(v_inst_1789_, 0);
                leanh::lean_inc_ref(v_toApplicative_1940_);
                v_toBind_1941_ = leanh::lean_ctor_get(v_inst_1789_, 1);
                leanh::lean_inc_n(v_toBind_1941_, 4);
                leanh::lean_dec_ref(v_inst_1789_);
                v_getRef_1942_ = leanh::lean_ctor_get(v_inst_1790_, 0);
                leanh::lean_inc(v_getRef_1942_);
                leanh::lean_dec_ref(v_inst_1790_);
                v_toPure_1943_ = leanh::lean_ctor_get(v_toApplicative_1940_, 1);
                leanh::lean_inc_n(v_toPure_1943_, 2);
                leanh::lean_dec_ref(v_toApplicative_1940_);
                v___f_1944_ = leanh::lean_alloc_closure(
                    l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_1944_, 0, v_toPure_1943_);
                leanh::lean_closure_set(v___f_1944_, 1, v_x_1792_);
                leanh::lean_inc_ref(v_inst_1791_);
                v___f_1945_ = leanh::lean_alloc_closure(
                    l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_1945_, 0, v_inst_1791_);
                leanh::lean_closure_set(v___f_1945_, 1, v_toBind_1941_);
                leanh::lean_closure_set(v___f_1945_, 2, v___f_1944_);
                v___f_1946_ = leanh::lean_alloc_closure(
                    l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_1946_, 0, v_inst_1791_);
                leanh::lean_closure_set(v___f_1946_, 1, v_toBind_1941_);
                leanh::lean_closure_set(v___f_1946_, 2, v___f_1945_);
                v___x_1947_ = leanh::lean_box((v___x_1939_) as usize);
                v___f_1948_ = leanh::lean_alloc_closure(
                    l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_1948_, 0, v___x_1947_);
                leanh::lean_closure_set(v___f_1948_, 1, v_toPure_1943_);
                v___x_1949_ = leanh::lean_apply_4(
                    v_toBind_1941_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_getRef_1942_,
                    v___f_1948_,
                );
                v___x_1950_ = leanh::lean_apply_4(
                    v_toBind_1941_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1949_,
                    v___f_1946_,
                );
                return v___x_1950_;
            } else {
                let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1954_: u8 = 0;
                v___x_1951_ = leanh::lean_unsigned_to_nat(1);
                v___x_1952_ = l_Lean_Syntax_getArg(v___x_1937_, v___x_1951_);
                leanh::lean_dec(v___x_1937_);
                v___x_1953_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14;
                leanh::lean_inc(v___x_1952_);
                v___x_1954_ = l_Lean_Syntax_isOfKind(v___x_1952_, v___x_1953_);
                if v___x_1954_ == 0 {
                    let mut v_toApplicative_1955_: *mut leanh::LeanObject =
                        core::ptr::null_mut();
                    let mut v_toBind_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_getRef_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_toPure_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___f_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___f_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___f_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___f_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v___x_1952_);
                    v_toApplicative_1955_ = leanh::lean_ctor_get(v_inst_1789_, 0);
                    leanh::lean_inc_ref(v_toApplicative_1955_);
                    v_toBind_1956_ = leanh::lean_ctor_get(v_inst_1789_, 1);
                    leanh::lean_inc_n(v_toBind_1956_, 4);
                    leanh::lean_dec_ref(v_inst_1789_);
                    v_getRef_1957_ = leanh::lean_ctor_get(v_inst_1790_, 0);
                    leanh::lean_inc(v_getRef_1957_);
                    leanh::lean_dec_ref(v_inst_1790_);
                    v_toPure_1958_ = leanh::lean_ctor_get(v_toApplicative_1955_, 1);
                    leanh::lean_inc_n(v_toPure_1958_, 2);
                    leanh::lean_dec_ref(v_toApplicative_1955_);
                    v___f_1959_ = leanh::lean_alloc_closure(
                        l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    leanh::lean_closure_set(v___f_1959_, 0, v_toPure_1958_);
                    leanh::lean_closure_set(v___f_1959_, 1, v_x_1792_);
                    leanh::lean_inc_ref(v_inst_1791_);
                    v___f_1960_ = leanh::lean_alloc_closure(
                        l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___f_1960_, 0, v_inst_1791_);
                    leanh::lean_closure_set(v___f_1960_, 1, v_toBind_1956_);
                    leanh::lean_closure_set(v___f_1960_, 2, v___f_1959_);
                    v___f_1961_ = leanh::lean_alloc_closure(
                        l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___f_1961_, 0, v_inst_1791_);
                    leanh::lean_closure_set(v___f_1961_, 1, v_toBind_1956_);
                    leanh::lean_closure_set(v___f_1961_, 2, v___f_1960_);
                    v___x_1962_ = leanh::lean_box((v___x_1954_) as usize);
                    v___f_1963_ = leanh::lean_alloc_closure(
                        l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    leanh::lean_closure_set(v___f_1963_, 0, v___x_1962_);
                    leanh::lean_closure_set(v___f_1963_, 1, v_toPure_1958_);
                    v___x_1964_ = leanh::lean_apply_4(
                        v_toBind_1956_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_getRef_1957_,
                        v___f_1963_,
                    );
                    v___x_1965_ = leanh::lean_apply_4(
                        v_toBind_1956_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1964_,
                        v___f_1961_,
                    );
                    return v___x_1965_;
                } else {
                    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1968_: u8 = 0;
                    v___x_1966_ = l_Lean_Syntax_getArg(v___x_1952_, v___x_1936_);
                    leanh::lean_dec(v___x_1952_);
                    v___x_1967_ = leanh::lean_box(0);
                    v___x_1968_ = l_Lean_Syntax_matchesIdent(v___x_1966_, v___x_1967_);
                    leanh::lean_dec(v___x_1966_);
                    if v___x_1968_ == 0 {
                        let mut v_toApplicative_1969_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_toBind_1970_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_getRef_1971_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_toPure_1972_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v___f_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___f_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___f_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___f_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_toApplicative_1969_ = leanh::lean_ctor_get(v_inst_1789_, 0);
                        leanh::lean_inc_ref(v_toApplicative_1969_);
                        v_toBind_1970_ = leanh::lean_ctor_get(v_inst_1789_, 1);
                        leanh::lean_inc_n(v_toBind_1970_, 4);
                        leanh::lean_dec_ref(v_inst_1789_);
                        v_getRef_1971_ = leanh::lean_ctor_get(v_inst_1790_, 0);
                        leanh::lean_inc(v_getRef_1971_);
                        leanh::lean_dec_ref(v_inst_1790_);
                        v_toPure_1972_ = leanh::lean_ctor_get(v_toApplicative_1969_, 1);
                        leanh::lean_inc_n(v_toPure_1972_, 2);
                        leanh::lean_dec_ref(v_toApplicative_1969_);
                        v___f_1973_ = leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        leanh::lean_closure_set(v___f_1973_, 0, v_toPure_1972_);
                        leanh::lean_closure_set(v___f_1973_, 1, v_x_1792_);
                        leanh::lean_inc_ref(v_inst_1791_);
                        v___f_1974_ = leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        leanh::lean_closure_set(v___f_1974_, 0, v_inst_1791_);
                        leanh::lean_closure_set(v___f_1974_, 1, v_toBind_1970_);
                        leanh::lean_closure_set(v___f_1974_, 2, v___f_1973_);
                        v___f_1975_ = leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        leanh::lean_closure_set(v___f_1975_, 0, v_inst_1791_);
                        leanh::lean_closure_set(v___f_1975_, 1, v_toBind_1970_);
                        leanh::lean_closure_set(v___f_1975_, 2, v___f_1974_);
                        v___x_1976_ = leanh::lean_box((v___x_1968_) as usize);
                        v___f_1977_ = leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        leanh::lean_closure_set(v___f_1977_, 0, v___x_1976_);
                        leanh::lean_closure_set(v___f_1977_, 1, v_toPure_1972_);
                        v___x_1978_ = leanh::lean_apply_4(
                            v_toBind_1970_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v_getRef_1971_,
                            v___f_1977_,
                        );
                        v___x_1979_ = leanh::lean_apply_4(
                            v_toBind_1970_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_1978_,
                            v___f_1975_,
                        );
                        return v___x_1979_;
                    } else {
                        let mut v_toApplicative_1980_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_toBind_1981_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_P_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___f_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_toApplicative_1980_ = leanh::lean_ctor_get(v_inst_1789_, 0);
                        v_toBind_1981_ = leanh::lean_ctor_get(v_inst_1789_, 1);
                        leanh::lean_inc_n(v_toBind_1981_, 2);
                        v_P_1982_ = l_Lean_Syntax_getArg(v_x_1792_, v___x_1951_);
                        leanh::lean_dec(v_x_1792_);
                        v___x_1983_ = leanh::lean_box((v___x_1796_) as usize);
                        leanh::lean_inc_ref(v_inst_1791_);
                        leanh::lean_inc_ref(v_toApplicative_1980_);
                        leanh::lean_inc_ref(v_inst_1790_);
                        v___f_1984_ = leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__18___boxed
                                as *mut core::ffi::c_void,
                            14,
                            13,
                        );
                        leanh::lean_closure_set(v___f_1984_, 0, v_inst_1790_);
                        leanh::lean_closure_set(v___f_1984_, 1, v_toApplicative_1980_);
                        leanh::lean_closure_set(v___f_1984_, 2, v_inst_1791_);
                        leanh::lean_closure_set(v___f_1984_, 3, v___x_1967_);
                        leanh::lean_closure_set(v___f_1984_, 4, v___x_1793_);
                        leanh::lean_closure_set(v___f_1984_, 5, v___x_1794_);
                        leanh::lean_closure_set(v___f_1984_, 6, v___x_1797_);
                        leanh::lean_closure_set(v___f_1984_, 7, v___x_1798_);
                        leanh::lean_closure_set(v___f_1984_, 8, v___x_1953_);
                        leanh::lean_closure_set(v___f_1984_, 9, v___x_1938_);
                        leanh::lean_closure_set(v___f_1984_, 10, v___x_1799_);
                        leanh::lean_closure_set(v___f_1984_, 11, v_toBind_1981_);
                        leanh::lean_closure_set(v___f_1984_, 12, v___x_1983_);
                        v___x_1985_ = l_Std_Do_SPred_Notation_unpack___redArg(
                            v_inst_1789_,
                            v_inst_1790_,
                            v_inst_1791_,
                            v_P_1982_,
                        );
                        v___x_1986_ = leanh::lean_apply_4(
                            v_toBind_1981_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_1985_,
                            v___f_1984_,
                        );
                        return v___x_1986_;
                    }
                }
            }
        }
    } else {
        let mut v_toApplicative_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_getRef_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1987_ = leanh::lean_ctor_get(v_inst_1789_, 0);
        leanh::lean_inc_ref(v_toApplicative_1987_);
        v_toBind_1988_ = leanh::lean_ctor_get(v_inst_1789_, 1);
        leanh::lean_inc_n(v_toBind_1988_, 4);
        leanh::lean_dec_ref(v_inst_1789_);
        v_getRef_1989_ = leanh::lean_ctor_get(v_inst_1790_, 0);
        leanh::lean_inc(v_getRef_1989_);
        leanh::lean_dec_ref(v_inst_1790_);
        v_toPure_1990_ = leanh::lean_ctor_get(v_toApplicative_1987_, 1);
        leanh::lean_inc_n(v_toPure_1990_, 2);
        leanh::lean_dec_ref(v_toApplicative_1987_);
        v___x_1991_ = leanh::lean_unsigned_to_nat(1);
        v___x_1992_ = l_Lean_Syntax_getArg(v_x_1792_, v___x_1991_);
        leanh::lean_dec(v_x_1792_);
        v___f_1993_ = leanh::lean_alloc_closure(
            l_Std_Do_SPred_Notation_unpack___redArg___lam__17___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_1993_, 0, v_toPure_1990_);
        leanh::lean_closure_set(v___f_1993_, 1, v___x_1992_);
        leanh::lean_inc_ref(v_inst_1791_);
        v___f_1994_ = leanh::lean_alloc_closure(
            l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_1994_, 0, v_inst_1791_);
        leanh::lean_closure_set(v___f_1994_, 1, v_toBind_1988_);
        leanh::lean_closure_set(v___f_1994_, 2, v___f_1993_);
        v___f_1995_ = leanh::lean_alloc_closure(
            l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_1995_, 0, v_inst_1791_);
        leanh::lean_closure_set(v___f_1995_, 1, v_toBind_1988_);
        leanh::lean_closure_set(v___f_1995_, 2, v___f_1994_);
        v___f_1996_ = leanh::lean_alloc_closure(
            l_Std_Do_SPred_Notation_unpack___redArg___lam__22___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_1996_, 0, v_toPure_1990_);
        v___x_1997_ = leanh::lean_apply_4(
            v_toBind_1988_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getRef_1989_,
            v___f_1996_,
        );
        v___x_1998_ = leanh::lean_apply_4(
            v_toBind_1988_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1997_,
            v___f_1995_,
        );
        return v___x_1998_;
    }
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__11(
    mut v_inst_1999_: *mut leanh::LeanObject,
    mut v_toApplicative_2000_: *mut leanh::LeanObject,
    mut v_inst_2001_: *mut leanh::LeanObject,
    mut v___x_2002_: *mut leanh::LeanObject,
    mut v___x_2003_: *mut leanh::LeanObject,
    mut v_toBind_2004_: *mut leanh::LeanObject,
    mut v___x_2005_: u8,
    mut v_inst_2006_: *mut leanh::LeanObject,
    mut v_e_2007_: *mut leanh::LeanObject,
    mut v_t_2008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2009_ = leanh::lean_box((v___x_2005_) as usize);
    leanh::lean_inc(v_toBind_2004_);
    leanh::lean_inc_ref(v_inst_2001_);
    leanh::lean_inc_ref(v_inst_1999_);
    v___f_2010_ = leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__13___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_2010_, 0, v_inst_1999_);
    leanh::lean_closure_set(v___f_2010_, 1, v_toApplicative_2000_);
    leanh::lean_closure_set(v___f_2010_, 2, v_inst_2001_);
    leanh::lean_closure_set(v___f_2010_, 3, v___x_2002_);
    leanh::lean_closure_set(v___f_2010_, 4, v___x_2003_);
    leanh::lean_closure_set(v___f_2010_, 5, v_t_2008_);
    leanh::lean_closure_set(v___f_2010_, 6, v_toBind_2004_);
    leanh::lean_closure_set(v___f_2010_, 7, v___x_2009_);
    v___x_2011_ = l_Std_Do_SPred_Notation_unpack___redArg(
        v_inst_2006_,
        v_inst_1999_,
        v_inst_2001_,
        v_e_2007_,
    );
    v___x_2012_ = leanh::lean_apply_4(
        v_toBind_2004_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2011_,
        v___f_2010_,
    );
    return v___x_2012_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack(
    mut v_m_2013_: *mut leanh::LeanObject,
    mut v_inst_2014_: *mut leanh::LeanObject,
    mut v_inst_2015_: *mut leanh::LeanObject,
    mut v_inst_2016_: *mut leanh::LeanObject,
    mut v_x_2017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2018_ = l_Std_Do_SPred_Notation_unpack___redArg(
        v_inst_2014_,
        v_inst_2015_,
        v_inst_2016_,
        v_x_2017_,
    );
    return v___x_2018_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Do_SPred_Notation_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Do_SPred_SPred(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Do_SPred_Notation_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Do_SPred_Notation_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Do_SPred_SPred(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Do_SPred_Notation_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Do_SPred_Notation_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Do_SPred_Notation_Basic(builtin);
}