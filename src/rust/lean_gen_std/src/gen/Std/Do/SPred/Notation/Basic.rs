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
pub static l_Std_Do_termSpred_x28___x29___closed__0_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [83, 116, 100, 0],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__1_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [68, 111, 0],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__2_value: crate::leanh::LeanStringObject<13> =
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
        m_data: [116, 101, 114, 109, 83, 112, 114, 101, 100, 40, 95, 41, 0],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Do_termSpred_x28___x29___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_Do_termSpred_x28___x29___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__1_value)
                as *mut crate::leanh::LeanObject,
            7300584325018775040 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_Do_termSpred_x28___x29___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__2_value)
                as *mut crate::leanh::LeanObject,
            13979102795498516556 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__4_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Std_Do_termSpred_x28___x29___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__4_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__6_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [115, 112, 114, 101, 100, 40, 0],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__7_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__8_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Std_Do_termSpred_x28___x29___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__8_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__10_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__9_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__12_value: crate::leanh::LeanStringObject<2> =
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
static mut l_Std_Do_termSpred_x28___x29___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__13_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__14_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__11_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do_termSpred_x28___x29___closed__15_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__3_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termSpred_x28___x29___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Do_termSpred_x28___x29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do_termTerm_x28___x29___closed__0_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [116, 101, 114, 109, 84, 101, 114, 109, 40, 95, 41, 0],
    };
static mut l_Std_Do_termTerm_x28___x29___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Do_termTerm_x28___x29___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Std_Do_termTerm_x28___x29___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__1_value)
                as *mut crate::leanh::LeanObject,
            7300584325018775040 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_Do_termTerm_x28___x29___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11926647143693398162 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termTerm_x28___x29___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do_termTerm_x28___x29___closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [116, 101, 114, 109, 40, 0],
    };
static mut l_Std_Do_termTerm_x28___x29___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do_termTerm_x28___x29___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termTerm_x28___x29___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do_termTerm_x28___x29___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termTerm_x28___x29___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do_termTerm_x28___x29___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termTerm_x28___x29___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do_termTerm_x28___x29___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Do_termTerm_x28___x29___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Do_termTerm_x28___x29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_termTerm_x28___x29___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__3_value) as *mut crate::leanh::LeanObject,7932075773091973500 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__5_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [102, 117, 110, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__5_value) as *mut crate::leanh::LeanObject;
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__5_value) as *mut crate::leanh::LeanObject,7043493786777132025 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__7_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 101, 114, 109, 73, 102, 84, 104, 101, 110, 69, 108, 115, 101, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__7_value) as *mut crate::leanh::LeanObject,14296711813398647265 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__9_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 121, 112, 101, 65, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__9_value) as *mut crate::leanh::LeanObject;
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__9_value) as *mut crate::leanh::LeanObject,5346268661279150583 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__11_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__11_value) as *mut crate::leanh::LeanObject;
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__11_value) as *mut crate::leanh::LeanObject,7306243862518720553 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__13_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__13_value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__16_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__18_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__18_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_termSpred_x28___x29___closed__1_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__19_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__18_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20_value) as *mut crate::leanh::LeanObject;
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__21_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__21_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__21_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20_value) as *mut crate::leanh::LeanObject,300274991653824376 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__22_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__21_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__22_value) as *mut crate::leanh::LeanObject;
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__23_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__23_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__23_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__24_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__23_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [77, 97, 99, 114, 111, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25_value) as *mut crate::leanh::LeanObject;
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__26_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__26_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__26_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25_value) as *mut crate::leanh::LeanObject,18105168627502861736 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__27_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__26_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__28_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__29_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__28_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__30_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__29_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__31_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__27_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__30_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__31_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__32_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__24_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__31_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__32_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__33_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__22_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__32_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__33_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__34_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__19_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__33_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__34: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__34_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__35_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__35: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__35_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__36_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__36_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__36_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__38_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 102, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__38: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__38_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__39_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 104, 101, 110, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__39: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__39_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__40_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [101, 108, 115, 101, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__40: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__40_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__41_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 97, 115, 105, 99, 70, 117, 110, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__41: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__41_value) as *mut crate::leanh::LeanObject;
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__41_value) as *mut crate::leanh::LeanObject,16077784126176397009 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42_value) as *mut crate::leanh::LeanObject;
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__44_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__44: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__44_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__0_value:
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
    m_data: [83, 80, 114, 101, 100, 0],
};
static mut l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__1_value:
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
    m_data: [78, 111, 116, 97, 116, 105, 111, 110, 0],
};
static mut l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__1___redArg(
    mut v_x_1066_: *mut crate::leanh::LeanObject,
    mut v_a_1067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: u8 = 0;
    v___x_1068_ = l_Std_Do_termSpred_x28___x29___closed__3;
    crate::leanh::lean_inc(v_x_1066_);
    v___x_1069_ = l_Lean_Syntax_isOfKind(v_x_1066_, v___x_1068_);
    if v___x_1069_ == 0 {
        let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1066_);
        v___x_1070_ = crate::leanh::lean_box(1);
        v___x_1071_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1071_, 0, v___x_1070_);
        crate::leanh::lean_ctor_set(v___x_1071_, 1, v_a_1067_);
        return v___x_1071_;
    } else {
        let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1075_: u8 = 0;
        v___x_1072_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1073_ = l_Lean_Syntax_getArg(v_x_1066_, v___x_1072_);
        crate::leanh::lean_dec(v_x_1066_);
        v___x_1074_ = l_Std_Do_termTerm_x28___x29___closed__1;
        crate::leanh::lean_inc(v___x_1073_);
        v___x_1075_ = l_Lean_Syntax_isOfKind(v___x_1073_, v___x_1074_);
        if v___x_1075_ == 0 {
            let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1076_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1076_, 0, v___x_1073_);
            crate::leanh::lean_ctor_set(v___x_1076_, 1, v_a_1067_);
            return v___x_1076_;
        } else {
            let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1077_ = l_Lean_Syntax_getArg(v___x_1073_, v___x_1072_);
            crate::leanh::lean_dec(v___x_1073_);
            v___x_1078_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1078_, 0, v___x_1077_);
            crate::leanh::lean_ctor_set(v___x_1078_, 1, v_a_1067_);
            return v___x_1078_;
        }
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__1(
    mut v_x_1079_: *mut crate::leanh::LeanObject,
    mut v_a_1080_: *mut crate::leanh::LeanObject,
    mut v_a_1081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1082_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__1___redArg(v_x_1079_, v_a_1081_);
    return v___x_1082_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__1___boxed(
    mut v_x_1083_: *mut crate::leanh::LeanObject,
    mut v_a_1084_: *mut crate::leanh::LeanObject,
    mut v_a_1085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1086_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__1(v_x_1083_, v_a_1084_, v_a_1085_);
    crate::leanh::lean_dec_ref(v_a_1084_);
    return v_res_1086_;
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1122_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__16;
    v___x_1123_ = l_String_toRawSubstring_x27(v___x_1122_);
    return v___x_1123_;
}
pub unsafe fn _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1178_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_1178_;
}
pub unsafe fn l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2(
    mut v_x_1180_: *mut crate::leanh::LeanObject,
    mut v_a_1181_: *mut crate::leanh::LeanObject,
    mut v_a_1182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: u8 = 0;
    v___x_1183_ = l_Std_Do_termSpred_x28___x29___closed__3;
    crate::leanh::lean_inc(v_x_1180_);
    v___x_1184_ = l_Lean_Syntax_isOfKind(v_x_1180_, v___x_1183_);
    if v___x_1184_ == 0 {
        let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1180_);
        v___x_1185_ = crate::leanh::lean_box(1);
        v___x_1186_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1186_, 0, v___x_1185_);
        crate::leanh::lean_ctor_set(v___x_1186_, 1, v_a_1182_);
        return v___x_1186_;
    } else {
        let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1191_: u8 = 0;
        v___x_1187_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1188_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1189_ = l_Lean_Syntax_getArg(v_x_1180_, v___x_1188_);
        crate::leanh::lean_dec(v_x_1180_);
        v___x_1190_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4;
        crate::leanh::lean_inc(v___x_1189_);
        v___x_1191_ = l_Lean_Syntax_isOfKind(v___x_1189_, v___x_1190_);
        if v___x_1191_ == 0 {
            let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1194_: u8 = 0;
            v___x_1192_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__5;
            v___x_1193_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6;
            crate::leanh::lean_inc(v___x_1189_);
            v___x_1194_ = l_Lean_Syntax_isOfKind(v___x_1189_, v___x_1193_);
            if v___x_1194_ == 0 {
                let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1196_: u8 = 0;
                v___x_1195_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__8;
                crate::leanh::lean_inc(v___x_1189_);
                v___x_1196_ = l_Lean_Syntax_isOfKind(v___x_1189_, v___x_1195_);
                if v___x_1196_ == 0 {
                    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1198_: u8 = 0;
                    v___x_1197_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10;
                    crate::leanh::lean_inc(v___x_1189_);
                    v___x_1198_ = l_Lean_Syntax_isOfKind(v___x_1189_, v___x_1197_);
                    if v___x_1198_ == 0 {
                        let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v___x_1189_);
                        v___x_1199_ = crate::leanh::lean_box(1);
                        v___x_1200_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1200_, 0, v___x_1199_);
                        crate::leanh::lean_ctor_set(v___x_1200_, 1, v_a_1182_);
                        return v___x_1200_;
                    } else {
                        let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1203_: u8 = 0;
                        v___x_1201_ = l_Lean_Syntax_getArg(v___x_1189_, v___x_1187_);
                        v___x_1202_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12;
                        crate::leanh::lean_inc(v___x_1201_);
                        v___x_1203_ = l_Lean_Syntax_isOfKind(v___x_1201_, v___x_1202_);
                        if v___x_1203_ == 0 {
                            let mut v___x_1204_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1205_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v___x_1201_);
                            crate::leanh::lean_dec(v___x_1189_);
                            v___x_1204_ = crate::leanh::lean_box(1);
                            v___x_1205_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1205_, 0, v___x_1204_);
                            crate::leanh::lean_ctor_set(v___x_1205_, 1, v_a_1182_);
                            return v___x_1205_;
                        } else {
                            let mut v___x_1206_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1207_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1208_: u8 = 0;
                            v___x_1206_ = l_Lean_Syntax_getArg(v___x_1201_, v___x_1188_);
                            crate::leanh::lean_dec(v___x_1201_);
                            v___x_1207_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14;
                            crate::leanh::lean_inc(v___x_1206_);
                            v___x_1208_ = l_Lean_Syntax_isOfKind(v___x_1206_, v___x_1207_);
                            if v___x_1208_ == 0 {
                                let mut v___x_1209_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1210_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                crate::leanh::lean_dec(v___x_1206_);
                                crate::leanh::lean_dec(v___x_1189_);
                                v___x_1209_ = crate::leanh::lean_box(1);
                                v___x_1210_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1210_, 0, v___x_1209_);
                                crate::leanh::lean_ctor_set(v___x_1210_, 1, v_a_1182_);
                                return v___x_1210_;
                            } else {
                                let mut v___x_1211_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1212_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1213_: u8 = 0;
                                v___x_1211_ = l_Lean_Syntax_getArg(v___x_1206_, v___x_1187_);
                                crate::leanh::lean_dec(v___x_1206_);
                                v___x_1212_ = crate::leanh::lean_box(0);
                                v___x_1213_ = l_Lean_Syntax_matchesIdent(v___x_1211_, v___x_1212_);
                                crate::leanh::lean_dec(v___x_1211_);
                                if v___x_1213_ == 0 {
                                    let mut v___x_1214_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1215_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    crate::leanh::lean_dec(v___x_1189_);
                                    v___x_1214_ = crate::leanh::lean_box(1);
                                    v___x_1215_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1215_, 0, v___x_1214_);
                                    crate::leanh::lean_ctor_set(v___x_1215_, 1, v_a_1182_);
                                    return v___x_1215_;
                                } else {
                                    let mut v___x_1216_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1217_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1218_: u8 = 0;
                                    v___x_1216_ = crate::leanh::lean_unsigned_to_nat(3);
                                    v___x_1217_ = l_Lean_Syntax_getArg(v___x_1189_, v___x_1216_);
                                    crate::leanh::lean_inc(v___x_1217_);
                                    v___x_1218_ =
                                        l_Lean_Syntax_matchesNull(v___x_1217_, v___x_1188_);
                                    if v___x_1218_ == 0 {
                                        let mut v___x_1219_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1220_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        crate::leanh::lean_dec(v___x_1217_);
                                        crate::leanh::lean_dec(v___x_1189_);
                                        v___x_1219_ = crate::leanh::lean_box(1);
                                        v___x_1220_ =
                                            crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_1220_, 0, v___x_1219_);
                                        crate::leanh::lean_ctor_set(v___x_1220_, 1, v_a_1182_);
                                        return v___x_1220_;
                                    } else {
                                        let mut v_quotContext_1221_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v_currMacroScope_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                        let mut v_ref_1223_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1224_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1225_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1226_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1227_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1228_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1229_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1230_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1231_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1232_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1233_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1234_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1235_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1236_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1237_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1238_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1239_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1240_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1241_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1242_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1243_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1244_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1245_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        v_quotContext_1221_ =
                                            crate::leanh::lean_ctor_get(v_a_1181_, 1);
                                        v_currMacroScope_1222_ =
                                            crate::leanh::lean_ctor_get(v_a_1181_, 2);
                                        v_ref_1223_ = crate::leanh::lean_ctor_get(v_a_1181_, 5);
                                        v___x_1224_ =
                                            l_Lean_Syntax_getArg(v___x_1189_, v___x_1188_);
                                        crate::leanh::lean_dec(v___x_1189_);
                                        v___x_1225_ =
                                            l_Lean_Syntax_getArg(v___x_1217_, v___x_1187_);
                                        crate::leanh::lean_dec(v___x_1217_);
                                        v___x_1226_ =
                                            l_Lean_SourceInfo_fromRef(v_ref_1223_, v___x_1196_);
                                        v___x_1227_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15;
                                        crate::leanh::lean_inc_n(v___x_1226_, 9);
                                        v___x_1228_ =
                                            crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_1228_, 0, v___x_1226_);
                                        crate::leanh::lean_ctor_set(v___x_1228_, 1, v___x_1227_);
                                        v___x_1229_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17_once), _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17);
                                        crate::leanh::lean_inc(v_currMacroScope_1222_);
                                        crate::leanh::lean_inc(v_quotContext_1221_);
                                        v___x_1230_ = l_Lean_addMacroScope(
                                            v_quotContext_1221_,
                                            v___x_1212_,
                                            v_currMacroScope_1222_,
                                        );
                                        v___x_1231_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__34;
                                        v___x_1232_ =
                                            crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_1232_, 0, v___x_1226_);
                                        crate::leanh::lean_ctor_set(v___x_1232_, 1, v___x_1229_);
                                        crate::leanh::lean_ctor_set(v___x_1232_, 2, v___x_1230_);
                                        crate::leanh::lean_ctor_set(v___x_1232_, 3, v___x_1231_);
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
                                            crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_1236_, 0, v___x_1226_);
                                        crate::leanh::lean_ctor_set(v___x_1236_, 1, v___x_1235_);
                                        v___x_1237_ = l_Std_Do_termSpred_x28___x29___closed__12;
                                        v___x_1238_ =
                                            crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_1238_, 0, v___x_1226_);
                                        crate::leanh::lean_ctor_set(v___x_1238_, 1, v___x_1237_);
                                        crate::leanh::lean_inc_ref(v___x_1238_);
                                        v___x_1239_ = l_Lean_Syntax_node3(
                                            v___x_1226_,
                                            v___x_1183_,
                                            v___x_1236_,
                                            v___x_1224_,
                                            v___x_1238_,
                                        );
                                        v___x_1240_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__35;
                                        v___x_1241_ =
                                            crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_1241_, 0, v___x_1226_);
                                        crate::leanh::lean_ctor_set(v___x_1241_, 1, v___x_1240_);
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
                                            crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_1245_, 0, v___x_1244_);
                                        crate::leanh::lean_ctor_set(v___x_1245_, 1, v_a_1182_);
                                        return v___x_1245_;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    let mut v_ref_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v_ref_1246_ = crate::leanh::lean_ctor_get(v_a_1181_, 5);
                    v___x_1247_ = l_Lean_Syntax_getArg(v___x_1189_, v___x_1188_);
                    v___x_1248_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1249_ = l_Lean_Syntax_getArg(v___x_1189_, v___x_1248_);
                    v___x_1250_ = crate::leanh::lean_unsigned_to_nat(5);
                    v___x_1251_ = l_Lean_Syntax_getArg(v___x_1189_, v___x_1250_);
                    crate::leanh::lean_dec(v___x_1189_);
                    v___x_1252_ = l_Lean_SourceInfo_fromRef(v_ref_1246_, v___x_1194_);
                    v___x_1253_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__38;
                    crate::leanh::lean_inc_n(v___x_1252_, 7);
                    v___x_1254_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1254_, 0, v___x_1252_);
                    crate::leanh::lean_ctor_set(v___x_1254_, 1, v___x_1253_);
                    v___x_1255_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__39;
                    v___x_1256_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1256_, 0, v___x_1252_);
                    crate::leanh::lean_ctor_set(v___x_1256_, 1, v___x_1255_);
                    v___x_1257_ = l_Std_Do_termSpred_x28___x29___closed__6;
                    v___x_1258_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1258_, 0, v___x_1252_);
                    crate::leanh::lean_ctor_set(v___x_1258_, 1, v___x_1257_);
                    v___x_1259_ = l_Std_Do_termSpred_x28___x29___closed__12;
                    v___x_1260_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1260_, 0, v___x_1252_);
                    crate::leanh::lean_ctor_set(v___x_1260_, 1, v___x_1259_);
                    crate::leanh::lean_inc_ref(v___x_1260_);
                    crate::leanh::lean_inc_ref(v___x_1258_);
                    v___x_1261_ = l_Lean_Syntax_node3(
                        v___x_1252_,
                        v___x_1183_,
                        v___x_1258_,
                        v___x_1249_,
                        v___x_1260_,
                    );
                    v___x_1262_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__40;
                    v___x_1263_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1263_, 0, v___x_1252_);
                    crate::leanh::lean_ctor_set(v___x_1263_, 1, v___x_1262_);
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
                    v___x_1266_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1266_, 0, v___x_1265_);
                    crate::leanh::lean_ctor_set(v___x_1266_, 1, v_a_1182_);
                    return v___x_1266_;
                }
            } else {
                let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1269_: u8 = 0;
                v___x_1267_ = l_Lean_Syntax_getArg(v___x_1189_, v___x_1188_);
                crate::leanh::lean_dec(v___x_1189_);
                v___x_1268_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42;
                crate::leanh::lean_inc(v___x_1267_);
                v___x_1269_ = l_Lean_Syntax_isOfKind(v___x_1267_, v___x_1268_);
                if v___x_1269_ == 0 {
                    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_1267_);
                    v___x_1270_ = crate::leanh::lean_box(1);
                    v___x_1271_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1271_, 0, v___x_1270_);
                    crate::leanh::lean_ctor_set(v___x_1271_, 1, v_a_1182_);
                    return v___x_1271_;
                } else {
                    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1273_: u8 = 0;
                    v___x_1272_ = l_Lean_Syntax_getArg(v___x_1267_, v___x_1188_);
                    v___x_1273_ = l_Lean_Syntax_matchesNull(v___x_1272_, v___x_1187_);
                    if v___x_1273_ == 0 {
                        let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v___x_1267_);
                        v___x_1274_ = crate::leanh::lean_box(1);
                        v___x_1275_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1275_, 0, v___x_1274_);
                        crate::leanh::lean_ctor_set(v___x_1275_, 1, v_a_1182_);
                        return v___x_1275_;
                    } else {
                        let mut v_ref_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_xs_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                        v_ref_1276_ = crate::leanh::lean_ctor_get(v_a_1181_, 5);
                        v___x_1277_ = l_Lean_Syntax_getArg(v___x_1267_, v___x_1187_);
                        v___x_1278_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_1279_ = l_Lean_Syntax_getArg(v___x_1267_, v___x_1278_);
                        crate::leanh::lean_dec(v___x_1267_);
                        v_xs_1280_ = l_Lean_Syntax_getArgs(v___x_1277_);
                        crate::leanh::lean_dec(v___x_1277_);
                        v___x_1281_ = l_Lean_SourceInfo_fromRef(v_ref_1276_, v___x_1191_);
                        crate::leanh::lean_inc_n(v___x_1281_, 8);
                        v___x_1282_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1282_, 0, v___x_1281_);
                        crate::leanh::lean_ctor_set(v___x_1282_, 1, v___x_1192_);
                        v___x_1283_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37;
                        v___x_1284_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43_once), _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43);
                        v___x_1285_ = l_Array_append___redArg(v___x_1284_, v_xs_1280_);
                        crate::leanh::lean_dec_ref(v_xs_1280_);
                        v___x_1286_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1286_, 0, v___x_1281_);
                        crate::leanh::lean_ctor_set(v___x_1286_, 1, v___x_1283_);
                        crate::leanh::lean_ctor_set(v___x_1286_, 2, v___x_1285_);
                        v___x_1287_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1287_, 0, v___x_1281_);
                        crate::leanh::lean_ctor_set(v___x_1287_, 1, v___x_1283_);
                        crate::leanh::lean_ctor_set(v___x_1287_, 2, v___x_1284_);
                        v___x_1288_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__44;
                        v___x_1289_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1289_, 0, v___x_1281_);
                        crate::leanh::lean_ctor_set(v___x_1289_, 1, v___x_1288_);
                        v___x_1290_ = l_Std_Do_termSpred_x28___x29___closed__6;
                        v___x_1291_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1291_, 0, v___x_1281_);
                        crate::leanh::lean_ctor_set(v___x_1291_, 1, v___x_1290_);
                        v___x_1292_ = l_Std_Do_termSpred_x28___x29___closed__12;
                        v___x_1293_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1293_, 0, v___x_1281_);
                        crate::leanh::lean_ctor_set(v___x_1293_, 1, v___x_1292_);
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
                        v___x_1297_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1297_, 0, v___x_1296_);
                        crate::leanh::lean_ctor_set(v___x_1297_, 1, v_a_1182_);
                        return v___x_1297_;
                    }
                }
            }
        } else {
            let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1300_: u8 = 0;
            v___x_1298_ = l_Lean_Syntax_getArg(v___x_1189_, v___x_1187_);
            v___x_1299_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12;
            crate::leanh::lean_inc(v___x_1298_);
            v___x_1300_ = l_Lean_Syntax_isOfKind(v___x_1298_, v___x_1299_);
            if v___x_1300_ == 0 {
                let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_1298_);
                crate::leanh::lean_dec(v___x_1189_);
                v___x_1301_ = crate::leanh::lean_box(1);
                v___x_1302_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1302_, 0, v___x_1301_);
                crate::leanh::lean_ctor_set(v___x_1302_, 1, v_a_1182_);
                return v___x_1302_;
            } else {
                let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1305_: u8 = 0;
                v___x_1303_ = l_Lean_Syntax_getArg(v___x_1298_, v___x_1188_);
                crate::leanh::lean_dec(v___x_1298_);
                v___x_1304_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14;
                crate::leanh::lean_inc(v___x_1303_);
                v___x_1305_ = l_Lean_Syntax_isOfKind(v___x_1303_, v___x_1304_);
                if v___x_1305_ == 0 {
                    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_1303_);
                    crate::leanh::lean_dec(v___x_1189_);
                    v___x_1306_ = crate::leanh::lean_box(1);
                    v___x_1307_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1307_, 0, v___x_1306_);
                    crate::leanh::lean_ctor_set(v___x_1307_, 1, v_a_1182_);
                    return v___x_1307_;
                } else {
                    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1310_: u8 = 0;
                    v___x_1308_ = l_Lean_Syntax_getArg(v___x_1303_, v___x_1187_);
                    crate::leanh::lean_dec(v___x_1303_);
                    v___x_1309_ = crate::leanh::lean_box(0);
                    v___x_1310_ = l_Lean_Syntax_matchesIdent(v___x_1308_, v___x_1309_);
                    crate::leanh::lean_dec(v___x_1308_);
                    if v___x_1310_ == 0 {
                        let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v___x_1189_);
                        v___x_1311_ = crate::leanh::lean_box(1);
                        v___x_1312_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1312_, 0, v___x_1311_);
                        crate::leanh::lean_ctor_set(v___x_1312_, 1, v_a_1182_);
                        return v___x_1312_;
                    } else {
                        let mut v_quotContext_1313_: *mut crate::leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_currMacroScope_1314_: *mut crate::leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_ref_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1317_: u8 = 0;
                        let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_quotContext_1313_ = crate::leanh::lean_ctor_get(v_a_1181_, 1);
                        v_currMacroScope_1314_ = crate::leanh::lean_ctor_get(v_a_1181_, 2);
                        v_ref_1315_ = crate::leanh::lean_ctor_get(v_a_1181_, 5);
                        v___x_1316_ = l_Lean_Syntax_getArg(v___x_1189_, v___x_1188_);
                        crate::leanh::lean_dec(v___x_1189_);
                        v___x_1317_ = 0;
                        v___x_1318_ = l_Lean_SourceInfo_fromRef(v_ref_1315_, v___x_1317_);
                        v___x_1319_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15;
                        crate::leanh::lean_inc_n(v___x_1318_, 7);
                        v___x_1320_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1320_, 0, v___x_1318_);
                        crate::leanh::lean_ctor_set(v___x_1320_, 1, v___x_1319_);
                        v___x_1321_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17_once), _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17);
                        crate::leanh::lean_inc(v_currMacroScope_1314_);
                        crate::leanh::lean_inc(v_quotContext_1313_);
                        v___x_1322_ = l_Lean_addMacroScope(
                            v_quotContext_1313_,
                            v___x_1309_,
                            v_currMacroScope_1314_,
                        );
                        v___x_1323_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__34;
                        v___x_1324_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1324_, 0, v___x_1318_);
                        crate::leanh::lean_ctor_set(v___x_1324_, 1, v___x_1321_);
                        crate::leanh::lean_ctor_set(v___x_1324_, 2, v___x_1322_);
                        crate::leanh::lean_ctor_set(v___x_1324_, 3, v___x_1323_);
                        v___x_1325_ = l_Lean_Syntax_node1(v___x_1318_, v___x_1304_, v___x_1324_);
                        v___x_1326_ =
                            l_Lean_Syntax_node2(v___x_1318_, v___x_1299_, v___x_1320_, v___x_1325_);
                        v___x_1327_ = l_Std_Do_termSpred_x28___x29___closed__6;
                        v___x_1328_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1328_, 0, v___x_1318_);
                        crate::leanh::lean_ctor_set(v___x_1328_, 1, v___x_1327_);
                        v___x_1329_ = l_Std_Do_termSpred_x28___x29___closed__12;
                        v___x_1330_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1330_, 0, v___x_1318_);
                        crate::leanh::lean_ctor_set(v___x_1330_, 1, v___x_1329_);
                        crate::leanh::lean_inc_ref(v___x_1330_);
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
                        v___x_1333_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1333_, 0, v___x_1332_);
                        crate::leanh::lean_ctor_set(v___x_1333_, 1, v_a_1182_);
                        return v___x_1333_;
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___boxed(
    mut v_x_1334_: *mut crate::leanh::LeanObject,
    mut v_a_1335_: *mut crate::leanh::LeanObject,
    mut v_a_1336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1337_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2(v_x_1334_, v_a_1335_, v_a_1336_);
    crate::leanh::lean_dec_ref(v_a_1335_);
    return v_res_1337_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__0(
    mut v_toPure_1338_: *mut crate::leanh::LeanObject,
    mut v_x_1339_: *mut crate::leanh::LeanObject,
    mut v_quotCtx_1340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1341_ = crate::leanh::lean_apply_2(v_toPure_1338_, crate::leanh::lean_box(0), v_x_1339_);
    return v___x_1341_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed(
    mut v_toPure_1342_: *mut crate::leanh::LeanObject,
    mut v_x_1343_: *mut crate::leanh::LeanObject,
    mut v_quotCtx_1344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1345_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__0(
        v_toPure_1342_,
        v_x_1343_,
        v_quotCtx_1344_,
    );
    crate::leanh::lean_dec(v_quotCtx_1344_);
    return v_res_1345_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__1(
    mut v_inst_1346_: *mut crate::leanh::LeanObject,
    mut v_toBind_1347_: *mut crate::leanh::LeanObject,
    mut v___f_1348_: *mut crate::leanh::LeanObject,
    mut v_scp_1349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getContext_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getContext_1350_ = crate::leanh::lean_ctor_get(v_inst_1346_, 2);
    crate::leanh::lean_inc(v_getContext_1350_);
    crate::leanh::lean_dec_ref(v_inst_1346_);
    v___x_1351_ = crate::leanh::lean_apply_4(
        v_toBind_1347_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getContext_1350_,
        v___f_1348_,
    );
    return v___x_1351_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed(
    mut v_inst_1352_: *mut crate::leanh::LeanObject,
    mut v_toBind_1353_: *mut crate::leanh::LeanObject,
    mut v___f_1354_: *mut crate::leanh::LeanObject,
    mut v_scp_1355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1356_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__1(
        v_inst_1352_,
        v_toBind_1353_,
        v___f_1354_,
        v_scp_1355_,
    );
    crate::leanh::lean_dec(v_scp_1355_);
    return v_res_1356_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__2(
    mut v_inst_1357_: *mut crate::leanh::LeanObject,
    mut v_toBind_1358_: *mut crate::leanh::LeanObject,
    mut v___f_1359_: *mut crate::leanh::LeanObject,
    mut v_info_1360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getCurrMacroScope_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getCurrMacroScope_1361_ = crate::leanh::lean_ctor_get(v_inst_1357_, 1);
    crate::leanh::lean_inc(v_getCurrMacroScope_1361_);
    crate::leanh::lean_dec_ref(v_inst_1357_);
    v___x_1362_ = crate::leanh::lean_apply_4(
        v_toBind_1358_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getCurrMacroScope_1361_,
        v___f_1359_,
    );
    return v___x_1362_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed(
    mut v_inst_1363_: *mut crate::leanh::LeanObject,
    mut v_toBind_1364_: *mut crate::leanh::LeanObject,
    mut v___f_1365_: *mut crate::leanh::LeanObject,
    mut v_info_1366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1367_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__2(
        v_inst_1363_,
        v_toBind_1364_,
        v___f_1365_,
        v_info_1366_,
    );
    crate::leanh::lean_dec(v_info_1366_);
    return v_res_1367_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__3(
    mut v___x_1368_: u8,
    mut v_toPure_1369_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1371_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1370_, v___x_1368_);
    v___x_1372_ =
        crate::leanh::lean_apply_2(v_toPure_1369_, crate::leanh::lean_box(0), v___x_1371_);
    return v___x_1372_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed(
    mut v___x_1373_: *mut crate::leanh::LeanObject,
    mut v_toPure_1374_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9844__boxed_1376_: u8 = 0;
    let mut v_res_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9844__boxed_1376_ = (crate::leanh::lean_unbox(v___x_1373_) as u8);
    v_res_1377_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__3(
        v___x_9844__boxed_1376_,
        v_toPure_1374_,
        v_____do__lift_1375_,
    );
    crate::leanh::lean_dec(v_____do__lift_1375_);
    return v_res_1377_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__20(
    mut v_info_1380_: *mut crate::leanh::LeanObject,
    mut v___x_1381_: *mut crate::leanh::LeanObject,
    mut v_scp_1382_: *mut crate::leanh::LeanObject,
    mut v___x_1383_: *mut crate::leanh::LeanObject,
    mut v___x_1384_: *mut crate::leanh::LeanObject,
    mut v___x_1385_: *mut crate::leanh::LeanObject,
    mut v___x_1386_: *mut crate::leanh::LeanObject,
    mut v___x_1387_: *mut crate::leanh::LeanObject,
    mut v___x_1388_: *mut crate::leanh::LeanObject,
    mut v___x_1389_: *mut crate::leanh::LeanObject,
    mut v___x_1390_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1391_: *mut crate::leanh::LeanObject,
    mut v_toPure_1392_: *mut crate::leanh::LeanObject,
    mut v_quotCtx_1393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1394_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15;
    crate::leanh::lean_inc_n(v_info_1380_, 7);
    v___x_1395_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1395_, 0, v_info_1380_);
    crate::leanh::lean_ctor_set(v___x_1395_, 1, v___x_1394_);
    v___x_1396_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17_once), _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17);
    v___x_1397_ = l_Lean_addMacroScope(v_quotCtx_1393_, v___x_1381_, v_scp_1382_);
    v___x_1398_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__0;
    v___x_1399_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__1;
    v___x_1400_ = l_Lean_Name_mkStr4(v___x_1383_, v___x_1384_, v___x_1398_, v___x_1399_);
    v___x_1401_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1401_, 0, v___x_1400_);
    v___x_1402_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20;
    crate::leanh::lean_inc_ref_n(v___x_1385_, 3);
    v___x_1403_ = l_Lean_Name_mkStr2(v___x_1385_, v___x_1402_);
    v___x_1404_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1404_, 0, v___x_1403_);
    v___x_1405_ = l_Lean_Name_mkStr2(v___x_1385_, v___x_1386_);
    v___x_1406_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1406_, 0, v___x_1405_);
    v___x_1407_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25;
    v___x_1408_ = l_Lean_Name_mkStr2(v___x_1385_, v___x_1407_);
    v___x_1409_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1409_, 0, v___x_1408_);
    v___x_1410_ = l_Lean_Name_mkStr1(v___x_1385_);
    v___x_1411_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1411_, 0, v___x_1410_);
    v___x_1412_ = crate::leanh::lean_box(0);
    v___x_1413_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1413_, 0, v___x_1411_);
    crate::leanh::lean_ctor_set(v___x_1413_, 1, v___x_1412_);
    v___x_1414_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1414_, 0, v___x_1409_);
    crate::leanh::lean_ctor_set(v___x_1414_, 1, v___x_1413_);
    v___x_1415_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1415_, 0, v___x_1406_);
    crate::leanh::lean_ctor_set(v___x_1415_, 1, v___x_1414_);
    v___x_1416_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1416_, 0, v___x_1404_);
    crate::leanh::lean_ctor_set(v___x_1416_, 1, v___x_1415_);
    v___x_1417_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1417_, 0, v___x_1401_);
    crate::leanh::lean_ctor_set(v___x_1417_, 1, v___x_1416_);
    v___x_1418_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1418_, 0, v_info_1380_);
    crate::leanh::lean_ctor_set(v___x_1418_, 1, v___x_1396_);
    crate::leanh::lean_ctor_set(v___x_1418_, 2, v___x_1397_);
    crate::leanh::lean_ctor_set(v___x_1418_, 3, v___x_1417_);
    v___x_1419_ = l_Lean_Syntax_node1(v_info_1380_, v___x_1387_, v___x_1418_);
    v___x_1420_ = l_Lean_Syntax_node2(v_info_1380_, v___x_1388_, v___x_1395_, v___x_1419_);
    v___x_1421_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__35;
    v___x_1422_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1422_, 0, v_info_1380_);
    crate::leanh::lean_ctor_set(v___x_1422_, 1, v___x_1421_);
    v___x_1423_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37;
    v___x_1424_ = l_Lean_Syntax_node1(v_info_1380_, v___x_1423_, v___x_1389_);
    v___x_1425_ = l_Std_Do_termSpred_x28___x29___closed__12;
    v___x_1426_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1426_, 0, v_info_1380_);
    crate::leanh::lean_ctor_set(v___x_1426_, 1, v___x_1425_);
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
        crate::leanh::lean_apply_2(v_toPure_1392_, crate::leanh::lean_box(0), v___x_1427_);
    return v___x_1428_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__4(
    mut v_info_1429_: *mut crate::leanh::LeanObject,
    mut v___x_1430_: *mut crate::leanh::LeanObject,
    mut v___x_1431_: *mut crate::leanh::LeanObject,
    mut v___x_1432_: *mut crate::leanh::LeanObject,
    mut v___x_1433_: *mut crate::leanh::LeanObject,
    mut v___x_1434_: *mut crate::leanh::LeanObject,
    mut v___x_1435_: *mut crate::leanh::LeanObject,
    mut v___x_1436_: *mut crate::leanh::LeanObject,
    mut v___x_1437_: *mut crate::leanh::LeanObject,
    mut v___x_1438_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1439_: *mut crate::leanh::LeanObject,
    mut v_toPure_1440_: *mut crate::leanh::LeanObject,
    mut v_toBind_1441_: *mut crate::leanh::LeanObject,
    mut v_getContext_1442_: *mut crate::leanh::LeanObject,
    mut v_scp_1443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1444_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__20 as *mut core::ffi::c_void,
        14,
        13,
    );
    crate::leanh::lean_closure_set(v___f_1444_, 0, v_info_1429_);
    crate::leanh::lean_closure_set(v___f_1444_, 1, v___x_1430_);
    crate::leanh::lean_closure_set(v___f_1444_, 2, v_scp_1443_);
    crate::leanh::lean_closure_set(v___f_1444_, 3, v___x_1431_);
    crate::leanh::lean_closure_set(v___f_1444_, 4, v___x_1432_);
    crate::leanh::lean_closure_set(v___f_1444_, 5, v___x_1433_);
    crate::leanh::lean_closure_set(v___f_1444_, 6, v___x_1434_);
    crate::leanh::lean_closure_set(v___f_1444_, 7, v___x_1435_);
    crate::leanh::lean_closure_set(v___f_1444_, 8, v___x_1436_);
    crate::leanh::lean_closure_set(v___f_1444_, 9, v___x_1437_);
    crate::leanh::lean_closure_set(v___f_1444_, 10, v___x_1438_);
    crate::leanh::lean_closure_set(v___f_1444_, 11, v_____do__lift_1439_);
    crate::leanh::lean_closure_set(v___f_1444_, 12, v_toPure_1440_);
    v___x_1445_ = crate::leanh::lean_apply_4(
        v_toBind_1441_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getContext_1442_,
        v___f_1444_,
    );
    return v___x_1445_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__5(
    mut v_inst_1446_: *mut crate::leanh::LeanObject,
    mut v___x_1447_: *mut crate::leanh::LeanObject,
    mut v___x_1448_: *mut crate::leanh::LeanObject,
    mut v___x_1449_: *mut crate::leanh::LeanObject,
    mut v___x_1450_: *mut crate::leanh::LeanObject,
    mut v___x_1451_: *mut crate::leanh::LeanObject,
    mut v___x_1452_: *mut crate::leanh::LeanObject,
    mut v___x_1453_: *mut crate::leanh::LeanObject,
    mut v___x_1454_: *mut crate::leanh::LeanObject,
    mut v___x_1455_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1456_: *mut crate::leanh::LeanObject,
    mut v_toPure_1457_: *mut crate::leanh::LeanObject,
    mut v_toBind_1458_: *mut crate::leanh::LeanObject,
    mut v_info_1459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getCurrMacroScope_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getContext_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getCurrMacroScope_1460_ = crate::leanh::lean_ctor_get(v_inst_1446_, 1);
    crate::leanh::lean_inc(v_getCurrMacroScope_1460_);
    v_getContext_1461_ = crate::leanh::lean_ctor_get(v_inst_1446_, 2);
    crate::leanh::lean_inc(v_getContext_1461_);
    crate::leanh::lean_dec_ref(v_inst_1446_);
    crate::leanh::lean_inc(v_toBind_1458_);
    v___f_1462_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__4 as *mut core::ffi::c_void,
        15,
        14,
    );
    crate::leanh::lean_closure_set(v___f_1462_, 0, v_info_1459_);
    crate::leanh::lean_closure_set(v___f_1462_, 1, v___x_1447_);
    crate::leanh::lean_closure_set(v___f_1462_, 2, v___x_1448_);
    crate::leanh::lean_closure_set(v___f_1462_, 3, v___x_1449_);
    crate::leanh::lean_closure_set(v___f_1462_, 4, v___x_1450_);
    crate::leanh::lean_closure_set(v___f_1462_, 5, v___x_1451_);
    crate::leanh::lean_closure_set(v___f_1462_, 6, v___x_1452_);
    crate::leanh::lean_closure_set(v___f_1462_, 7, v___x_1453_);
    crate::leanh::lean_closure_set(v___f_1462_, 8, v___x_1454_);
    crate::leanh::lean_closure_set(v___f_1462_, 9, v___x_1455_);
    crate::leanh::lean_closure_set(v___f_1462_, 10, v_____do__lift_1456_);
    crate::leanh::lean_closure_set(v___f_1462_, 11, v_toPure_1457_);
    crate::leanh::lean_closure_set(v___f_1462_, 12, v_toBind_1458_);
    crate::leanh::lean_closure_set(v___f_1462_, 13, v_getContext_1461_);
    v___x_1463_ = crate::leanh::lean_apply_4(
        v_toBind_1458_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getCurrMacroScope_1460_,
        v___f_1462_,
    );
    return v___x_1463_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__7(
    mut v_inst_1464_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1465_: *mut crate::leanh::LeanObject,
    mut v_inst_1466_: *mut crate::leanh::LeanObject,
    mut v___x_1467_: *mut crate::leanh::LeanObject,
    mut v___x_1468_: *mut crate::leanh::LeanObject,
    mut v___x_1469_: *mut crate::leanh::LeanObject,
    mut v___x_1470_: *mut crate::leanh::LeanObject,
    mut v___x_1471_: *mut crate::leanh::LeanObject,
    mut v___x_1472_: *mut crate::leanh::LeanObject,
    mut v___x_1473_: *mut crate::leanh::LeanObject,
    mut v___x_1474_: *mut crate::leanh::LeanObject,
    mut v___x_1475_: *mut crate::leanh::LeanObject,
    mut v_toBind_1476_: *mut crate::leanh::LeanObject,
    mut v___x_1477_: u8,
    mut v_____do__lift_1478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getRef_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getRef_1479_ = crate::leanh::lean_ctor_get(v_inst_1464_, 0);
    crate::leanh::lean_inc(v_getRef_1479_);
    crate::leanh::lean_dec_ref(v_inst_1464_);
    v_toPure_1480_ = crate::leanh::lean_ctor_get(v_toApplicative_1465_, 1);
    crate::leanh::lean_inc_n(v_toPure_1480_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_1465_);
    crate::leanh::lean_inc_n(v_toBind_1476_, 2);
    v___f_1481_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__5 as *mut core::ffi::c_void,
        14,
        13,
    );
    crate::leanh::lean_closure_set(v___f_1481_, 0, v_inst_1466_);
    crate::leanh::lean_closure_set(v___f_1481_, 1, v___x_1467_);
    crate::leanh::lean_closure_set(v___f_1481_, 2, v___x_1468_);
    crate::leanh::lean_closure_set(v___f_1481_, 3, v___x_1469_);
    crate::leanh::lean_closure_set(v___f_1481_, 4, v___x_1470_);
    crate::leanh::lean_closure_set(v___f_1481_, 5, v___x_1471_);
    crate::leanh::lean_closure_set(v___f_1481_, 6, v___x_1472_);
    crate::leanh::lean_closure_set(v___f_1481_, 7, v___x_1473_);
    crate::leanh::lean_closure_set(v___f_1481_, 8, v___x_1474_);
    crate::leanh::lean_closure_set(v___f_1481_, 9, v___x_1475_);
    crate::leanh::lean_closure_set(v___f_1481_, 10, v_____do__lift_1478_);
    crate::leanh::lean_closure_set(v___f_1481_, 11, v_toPure_1480_);
    crate::leanh::lean_closure_set(v___f_1481_, 12, v_toBind_1476_);
    v___x_1482_ = crate::leanh::lean_box((v___x_1477_) as usize);
    v___f_1483_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1483_, 0, v___x_1482_);
    crate::leanh::lean_closure_set(v___f_1483_, 1, v_toPure_1480_);
    v___x_1484_ = crate::leanh::lean_apply_4(
        v_toBind_1476_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRef_1479_,
        v___f_1483_,
    );
    v___x_1485_ = crate::leanh::lean_apply_4(
        v_toBind_1476_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1484_,
        v___f_1481_,
    );
    return v___x_1485_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__7___boxed(
    mut v_inst_1486_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1487_: *mut crate::leanh::LeanObject,
    mut v_inst_1488_: *mut crate::leanh::LeanObject,
    mut v___x_1489_: *mut crate::leanh::LeanObject,
    mut v___x_1490_: *mut crate::leanh::LeanObject,
    mut v___x_1491_: *mut crate::leanh::LeanObject,
    mut v___x_1492_: *mut crate::leanh::LeanObject,
    mut v___x_1493_: *mut crate::leanh::LeanObject,
    mut v___x_1494_: *mut crate::leanh::LeanObject,
    mut v___x_1495_: *mut crate::leanh::LeanObject,
    mut v___x_1496_: *mut crate::leanh::LeanObject,
    mut v___x_1497_: *mut crate::leanh::LeanObject,
    mut v_toBind_1498_: *mut crate::leanh::LeanObject,
    mut v___x_1499_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_10034__boxed_1501_: u8 = 0;
    let mut v_res_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_10034__boxed_1501_ = (crate::leanh::lean_unbox(v___x_1499_) as u8);
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
    mut v_info_1503_: *mut crate::leanh::LeanObject,
    mut v___x_1504_: *mut crate::leanh::LeanObject,
    mut v_xs_1505_: *mut crate::leanh::LeanObject,
    mut v___x_1506_: *mut crate::leanh::LeanObject,
    mut v_b_1507_: *mut crate::leanh::LeanObject,
    mut v___x_1508_: *mut crate::leanh::LeanObject,
    mut v_toPure_1509_: *mut crate::leanh::LeanObject,
    mut v_quotCtx_1510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_n(v_info_1503_, 5);
    v___x_1511_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1511_, 0, v_info_1503_);
    crate::leanh::lean_ctor_set(v___x_1511_, 1, v___x_1504_);
    v___x_1512_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__37;
    v___x_1513_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43_once), _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__43);
    v___x_1514_ = l_Array_append___redArg(v___x_1513_, v_xs_1505_);
    v___x_1515_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1515_, 0, v_info_1503_);
    crate::leanh::lean_ctor_set(v___x_1515_, 1, v___x_1512_);
    crate::leanh::lean_ctor_set(v___x_1515_, 2, v___x_1514_);
    v___x_1516_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1516_, 0, v_info_1503_);
    crate::leanh::lean_ctor_set(v___x_1516_, 1, v___x_1512_);
    crate::leanh::lean_ctor_set(v___x_1516_, 2, v___x_1513_);
    v___x_1517_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__44;
    v___x_1518_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1518_, 0, v_info_1503_);
    crate::leanh::lean_ctor_set(v___x_1518_, 1, v___x_1517_);
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
        crate::leanh::lean_apply_2(v_toPure_1509_, crate::leanh::lean_box(0), v___x_1520_);
    return v___x_1521_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__15___boxed(
    mut v_info_1522_: *mut crate::leanh::LeanObject,
    mut v___x_1523_: *mut crate::leanh::LeanObject,
    mut v_xs_1524_: *mut crate::leanh::LeanObject,
    mut v___x_1525_: *mut crate::leanh::LeanObject,
    mut v_b_1526_: *mut crate::leanh::LeanObject,
    mut v___x_1527_: *mut crate::leanh::LeanObject,
    mut v_toPure_1528_: *mut crate::leanh::LeanObject,
    mut v_quotCtx_1529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_quotCtx_1529_);
    crate::leanh::lean_dec_ref(v_xs_1524_);
    return v_res_1530_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__6(
    mut v_toBind_1531_: *mut crate::leanh::LeanObject,
    mut v_getContext_1532_: *mut crate::leanh::LeanObject,
    mut v___f_1533_: *mut crate::leanh::LeanObject,
    mut v_scp_1534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1535_ = crate::leanh::lean_apply_4(
        v_toBind_1531_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getContext_1532_,
        v___f_1533_,
    );
    return v___x_1535_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__6___boxed(
    mut v_toBind_1536_: *mut crate::leanh::LeanObject,
    mut v_getContext_1537_: *mut crate::leanh::LeanObject,
    mut v___f_1538_: *mut crate::leanh::LeanObject,
    mut v_scp_1539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1540_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__6(
        v_toBind_1536_,
        v_getContext_1537_,
        v___f_1538_,
        v_scp_1539_,
    );
    crate::leanh::lean_dec(v_scp_1539_);
    return v_res_1540_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__8(
    mut v_inst_1541_: *mut crate::leanh::LeanObject,
    mut v___x_1542_: *mut crate::leanh::LeanObject,
    mut v_xs_1543_: *mut crate::leanh::LeanObject,
    mut v___x_1544_: *mut crate::leanh::LeanObject,
    mut v_b_1545_: *mut crate::leanh::LeanObject,
    mut v___x_1546_: *mut crate::leanh::LeanObject,
    mut v_toPure_1547_: *mut crate::leanh::LeanObject,
    mut v_toBind_1548_: *mut crate::leanh::LeanObject,
    mut v_info_1549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getCurrMacroScope_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getContext_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getCurrMacroScope_1550_ = crate::leanh::lean_ctor_get(v_inst_1541_, 1);
    crate::leanh::lean_inc(v_getCurrMacroScope_1550_);
    v_getContext_1551_ = crate::leanh::lean_ctor_get(v_inst_1541_, 2);
    crate::leanh::lean_inc(v_getContext_1551_);
    crate::leanh::lean_dec_ref(v_inst_1541_);
    v___f_1552_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__15___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_1552_, 0, v_info_1549_);
    crate::leanh::lean_closure_set(v___f_1552_, 1, v___x_1542_);
    crate::leanh::lean_closure_set(v___f_1552_, 2, v_xs_1543_);
    crate::leanh::lean_closure_set(v___f_1552_, 3, v___x_1544_);
    crate::leanh::lean_closure_set(v___f_1552_, 4, v_b_1545_);
    crate::leanh::lean_closure_set(v___f_1552_, 5, v___x_1546_);
    crate::leanh::lean_closure_set(v___f_1552_, 6, v_toPure_1547_);
    crate::leanh::lean_inc(v_toBind_1548_);
    v___f_1553_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__6___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1553_, 0, v_toBind_1548_);
    crate::leanh::lean_closure_set(v___f_1553_, 1, v_getContext_1551_);
    crate::leanh::lean_closure_set(v___f_1553_, 2, v___f_1552_);
    v___x_1554_ = crate::leanh::lean_apply_4(
        v_toBind_1548_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getCurrMacroScope_1550_,
        v___f_1553_,
    );
    return v___x_1554_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__10(
    mut v_inst_1555_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1556_: *mut crate::leanh::LeanObject,
    mut v_inst_1557_: *mut crate::leanh::LeanObject,
    mut v___x_1558_: *mut crate::leanh::LeanObject,
    mut v_xs_1559_: *mut crate::leanh::LeanObject,
    mut v___x_1560_: *mut crate::leanh::LeanObject,
    mut v___x_1561_: *mut crate::leanh::LeanObject,
    mut v_toBind_1562_: *mut crate::leanh::LeanObject,
    mut v___x_1563_: u8,
    mut v_b_1564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getRef_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getRef_1565_ = crate::leanh::lean_ctor_get(v_inst_1555_, 0);
    crate::leanh::lean_inc(v_getRef_1565_);
    crate::leanh::lean_dec_ref(v_inst_1555_);
    v_toPure_1566_ = crate::leanh::lean_ctor_get(v_toApplicative_1556_, 1);
    crate::leanh::lean_inc_n(v_toPure_1566_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_1556_);
    crate::leanh::lean_inc_n(v_toBind_1562_, 2);
    v___f_1567_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__8 as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_1567_, 0, v_inst_1557_);
    crate::leanh::lean_closure_set(v___f_1567_, 1, v___x_1558_);
    crate::leanh::lean_closure_set(v___f_1567_, 2, v_xs_1559_);
    crate::leanh::lean_closure_set(v___f_1567_, 3, v___x_1560_);
    crate::leanh::lean_closure_set(v___f_1567_, 4, v_b_1564_);
    crate::leanh::lean_closure_set(v___f_1567_, 5, v___x_1561_);
    crate::leanh::lean_closure_set(v___f_1567_, 6, v_toPure_1566_);
    crate::leanh::lean_closure_set(v___f_1567_, 7, v_toBind_1562_);
    v___x_1568_ = crate::leanh::lean_box((v___x_1563_) as usize);
    v___f_1569_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1569_, 0, v___x_1568_);
    crate::leanh::lean_closure_set(v___f_1569_, 1, v_toPure_1566_);
    v___x_1570_ = crate::leanh::lean_apply_4(
        v_toBind_1562_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRef_1565_,
        v___f_1569_,
    );
    v___x_1571_ = crate::leanh::lean_apply_4(
        v_toBind_1562_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1570_,
        v___f_1567_,
    );
    return v___x_1571_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__10___boxed(
    mut v_inst_1572_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1573_: *mut crate::leanh::LeanObject,
    mut v_inst_1574_: *mut crate::leanh::LeanObject,
    mut v___x_1575_: *mut crate::leanh::LeanObject,
    mut v_xs_1576_: *mut crate::leanh::LeanObject,
    mut v___x_1577_: *mut crate::leanh::LeanObject,
    mut v___x_1578_: *mut crate::leanh::LeanObject,
    mut v_toBind_1579_: *mut crate::leanh::LeanObject,
    mut v___x_1580_: *mut crate::leanh::LeanObject,
    mut v_b_1581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_10144__boxed_1582_: u8 = 0;
    let mut v_res_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_10144__boxed_1582_ = (crate::leanh::lean_unbox(v___x_1580_) as u8);
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
    mut v_info_1584_: *mut crate::leanh::LeanObject,
    mut v___x_1585_: *mut crate::leanh::LeanObject,
    mut v___x_1586_: *mut crate::leanh::LeanObject,
    mut v_t_1587_: *mut crate::leanh::LeanObject,
    mut v_e_1588_: *mut crate::leanh::LeanObject,
    mut v_toPure_1589_: *mut crate::leanh::LeanObject,
    mut v_quotCtx_1590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1591_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__38;
    crate::leanh::lean_inc_n(v_info_1584_, 3);
    v___x_1592_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1592_, 0, v_info_1584_);
    crate::leanh::lean_ctor_set(v___x_1592_, 1, v___x_1591_);
    v___x_1593_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__39;
    v___x_1594_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1594_, 0, v_info_1584_);
    crate::leanh::lean_ctor_set(v___x_1594_, 1, v___x_1593_);
    v___x_1595_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__40;
    v___x_1596_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1596_, 0, v_info_1584_);
    crate::leanh::lean_ctor_set(v___x_1596_, 1, v___x_1595_);
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
        crate::leanh::lean_apply_2(v_toPure_1589_, crate::leanh::lean_box(0), v___x_1597_);
    return v___x_1598_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__9___boxed(
    mut v_info_1599_: *mut crate::leanh::LeanObject,
    mut v___x_1600_: *mut crate::leanh::LeanObject,
    mut v___x_1601_: *mut crate::leanh::LeanObject,
    mut v_t_1602_: *mut crate::leanh::LeanObject,
    mut v_e_1603_: *mut crate::leanh::LeanObject,
    mut v_toPure_1604_: *mut crate::leanh::LeanObject,
    mut v_quotCtx_1605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1606_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__9(
        v_info_1599_,
        v___x_1600_,
        v___x_1601_,
        v_t_1602_,
        v_e_1603_,
        v_toPure_1604_,
        v_quotCtx_1605_,
    );
    crate::leanh::lean_dec(v_quotCtx_1605_);
    return v_res_1606_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__12(
    mut v_inst_1607_: *mut crate::leanh::LeanObject,
    mut v___x_1608_: *mut crate::leanh::LeanObject,
    mut v___x_1609_: *mut crate::leanh::LeanObject,
    mut v_t_1610_: *mut crate::leanh::LeanObject,
    mut v_e_1611_: *mut crate::leanh::LeanObject,
    mut v_toPure_1612_: *mut crate::leanh::LeanObject,
    mut v_toBind_1613_: *mut crate::leanh::LeanObject,
    mut v_info_1614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getCurrMacroScope_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getContext_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getCurrMacroScope_1615_ = crate::leanh::lean_ctor_get(v_inst_1607_, 1);
    crate::leanh::lean_inc(v_getCurrMacroScope_1615_);
    v_getContext_1616_ = crate::leanh::lean_ctor_get(v_inst_1607_, 2);
    crate::leanh::lean_inc(v_getContext_1616_);
    crate::leanh::lean_dec_ref(v_inst_1607_);
    v___f_1617_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__9___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_1617_, 0, v_info_1614_);
    crate::leanh::lean_closure_set(v___f_1617_, 1, v___x_1608_);
    crate::leanh::lean_closure_set(v___f_1617_, 2, v___x_1609_);
    crate::leanh::lean_closure_set(v___f_1617_, 3, v_t_1610_);
    crate::leanh::lean_closure_set(v___f_1617_, 4, v_e_1611_);
    crate::leanh::lean_closure_set(v___f_1617_, 5, v_toPure_1612_);
    crate::leanh::lean_inc(v_toBind_1613_);
    v___f_1618_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__6___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1618_, 0, v_toBind_1613_);
    crate::leanh::lean_closure_set(v___f_1618_, 1, v_getContext_1616_);
    crate::leanh::lean_closure_set(v___f_1618_, 2, v___f_1617_);
    v___x_1619_ = crate::leanh::lean_apply_4(
        v_toBind_1613_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getCurrMacroScope_1615_,
        v___f_1618_,
    );
    return v___x_1619_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__13(
    mut v_inst_1620_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1621_: *mut crate::leanh::LeanObject,
    mut v_inst_1622_: *mut crate::leanh::LeanObject,
    mut v___x_1623_: *mut crate::leanh::LeanObject,
    mut v___x_1624_: *mut crate::leanh::LeanObject,
    mut v_t_1625_: *mut crate::leanh::LeanObject,
    mut v_toBind_1626_: *mut crate::leanh::LeanObject,
    mut v___x_1627_: u8,
    mut v_e_1628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getRef_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getRef_1629_ = crate::leanh::lean_ctor_get(v_inst_1620_, 0);
    crate::leanh::lean_inc(v_getRef_1629_);
    crate::leanh::lean_dec_ref(v_inst_1620_);
    v_toPure_1630_ = crate::leanh::lean_ctor_get(v_toApplicative_1621_, 1);
    crate::leanh::lean_inc_n(v_toPure_1630_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_1621_);
    crate::leanh::lean_inc_n(v_toBind_1626_, 2);
    v___f_1631_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__12 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_1631_, 0, v_inst_1622_);
    crate::leanh::lean_closure_set(v___f_1631_, 1, v___x_1623_);
    crate::leanh::lean_closure_set(v___f_1631_, 2, v___x_1624_);
    crate::leanh::lean_closure_set(v___f_1631_, 3, v_t_1625_);
    crate::leanh::lean_closure_set(v___f_1631_, 4, v_e_1628_);
    crate::leanh::lean_closure_set(v___f_1631_, 5, v_toPure_1630_);
    crate::leanh::lean_closure_set(v___f_1631_, 6, v_toBind_1626_);
    v___x_1632_ = crate::leanh::lean_box((v___x_1627_) as usize);
    v___f_1633_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1633_, 0, v___x_1632_);
    crate::leanh::lean_closure_set(v___f_1633_, 1, v_toPure_1630_);
    v___x_1634_ = crate::leanh::lean_apply_4(
        v_toBind_1626_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRef_1629_,
        v___f_1633_,
    );
    v___x_1635_ = crate::leanh::lean_apply_4(
        v_toBind_1626_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1634_,
        v___f_1631_,
    );
    return v___x_1635_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__13___boxed(
    mut v_inst_1636_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1637_: *mut crate::leanh::LeanObject,
    mut v_inst_1638_: *mut crate::leanh::LeanObject,
    mut v___x_1639_: *mut crate::leanh::LeanObject,
    mut v___x_1640_: *mut crate::leanh::LeanObject,
    mut v_t_1641_: *mut crate::leanh::LeanObject,
    mut v_toBind_1642_: *mut crate::leanh::LeanObject,
    mut v___x_1643_: *mut crate::leanh::LeanObject,
    mut v_e_1644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_10216__boxed_1645_: u8 = 0;
    let mut v_res_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_10216__boxed_1645_ = (crate::leanh::lean_unbox(v___x_1643_) as u8);
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
    mut v_info_1647_: *mut crate::leanh::LeanObject,
    mut v___x_1648_: *mut crate::leanh::LeanObject,
    mut v_scp_1649_: *mut crate::leanh::LeanObject,
    mut v___x_1650_: *mut crate::leanh::LeanObject,
    mut v___x_1651_: *mut crate::leanh::LeanObject,
    mut v___x_1652_: *mut crate::leanh::LeanObject,
    mut v___x_1653_: *mut crate::leanh::LeanObject,
    mut v___x_1654_: *mut crate::leanh::LeanObject,
    mut v___x_1655_: *mut crate::leanh::LeanObject,
    mut v___x_1656_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1657_: *mut crate::leanh::LeanObject,
    mut v_toPure_1658_: *mut crate::leanh::LeanObject,
    mut v_quotCtx_1659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1660_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__15;
    crate::leanh::lean_inc_n(v_info_1647_, 5);
    v___x_1661_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1661_, 0, v_info_1647_);
    crate::leanh::lean_ctor_set(v___x_1661_, 1, v___x_1660_);
    v___x_1662_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17), core::ptr::addr_of_mut!(l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17_once), _init_l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__17);
    v___x_1663_ = l_Lean_addMacroScope(v_quotCtx_1659_, v___x_1648_, v_scp_1649_);
    v___x_1664_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__0;
    v___x_1665_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__20___closed__1;
    v___x_1666_ = l_Lean_Name_mkStr4(v___x_1650_, v___x_1651_, v___x_1664_, v___x_1665_);
    v___x_1667_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1667_, 0, v___x_1666_);
    v___x_1668_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__20;
    crate::leanh::lean_inc_ref_n(v___x_1652_, 3);
    v___x_1669_ = l_Lean_Name_mkStr2(v___x_1652_, v___x_1668_);
    v___x_1670_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1670_, 0, v___x_1669_);
    v___x_1671_ = l_Lean_Name_mkStr2(v___x_1652_, v___x_1653_);
    v___x_1672_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1672_, 0, v___x_1671_);
    v___x_1673_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__25;
    v___x_1674_ = l_Lean_Name_mkStr2(v___x_1652_, v___x_1673_);
    v___x_1675_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1675_, 0, v___x_1674_);
    v___x_1676_ = l_Lean_Name_mkStr1(v___x_1652_);
    v___x_1677_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1677_, 0, v___x_1676_);
    v___x_1678_ = crate::leanh::lean_box(0);
    v___x_1679_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1679_, 0, v___x_1677_);
    crate::leanh::lean_ctor_set(v___x_1679_, 1, v___x_1678_);
    v___x_1680_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1680_, 0, v___x_1675_);
    crate::leanh::lean_ctor_set(v___x_1680_, 1, v___x_1679_);
    v___x_1681_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1681_, 0, v___x_1672_);
    crate::leanh::lean_ctor_set(v___x_1681_, 1, v___x_1680_);
    v___x_1682_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1682_, 0, v___x_1670_);
    crate::leanh::lean_ctor_set(v___x_1682_, 1, v___x_1681_);
    v___x_1683_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1683_, 0, v___x_1667_);
    crate::leanh::lean_ctor_set(v___x_1683_, 1, v___x_1682_);
    v___x_1684_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1684_, 0, v_info_1647_);
    crate::leanh::lean_ctor_set(v___x_1684_, 1, v___x_1662_);
    crate::leanh::lean_ctor_set(v___x_1684_, 2, v___x_1663_);
    crate::leanh::lean_ctor_set(v___x_1684_, 3, v___x_1683_);
    v___x_1685_ = l_Lean_Syntax_node1(v_info_1647_, v___x_1654_, v___x_1684_);
    v___x_1686_ = l_Lean_Syntax_node2(v_info_1647_, v___x_1655_, v___x_1661_, v___x_1685_);
    v___x_1687_ = l_Std_Do_termSpred_x28___x29___closed__12;
    v___x_1688_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1688_, 0, v_info_1647_);
    crate::leanh::lean_ctor_set(v___x_1688_, 1, v___x_1687_);
    v___x_1689_ = l_Lean_Syntax_node3(
        v_info_1647_,
        v___x_1656_,
        v___x_1686_,
        v_____do__lift_1657_,
        v___x_1688_,
    );
    v___x_1690_ =
        crate::leanh::lean_apply_2(v_toPure_1658_, crate::leanh::lean_box(0), v___x_1689_);
    return v___x_1690_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__14(
    mut v_info_1691_: *mut crate::leanh::LeanObject,
    mut v___x_1692_: *mut crate::leanh::LeanObject,
    mut v___x_1693_: *mut crate::leanh::LeanObject,
    mut v___x_1694_: *mut crate::leanh::LeanObject,
    mut v___x_1695_: *mut crate::leanh::LeanObject,
    mut v___x_1696_: *mut crate::leanh::LeanObject,
    mut v___x_1697_: *mut crate::leanh::LeanObject,
    mut v___x_1698_: *mut crate::leanh::LeanObject,
    mut v___x_1699_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1700_: *mut crate::leanh::LeanObject,
    mut v_toPure_1701_: *mut crate::leanh::LeanObject,
    mut v_toBind_1702_: *mut crate::leanh::LeanObject,
    mut v_getContext_1703_: *mut crate::leanh::LeanObject,
    mut v_scp_1704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1705_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__28 as *mut core::ffi::c_void,
        13,
        12,
    );
    crate::leanh::lean_closure_set(v___f_1705_, 0, v_info_1691_);
    crate::leanh::lean_closure_set(v___f_1705_, 1, v___x_1692_);
    crate::leanh::lean_closure_set(v___f_1705_, 2, v_scp_1704_);
    crate::leanh::lean_closure_set(v___f_1705_, 3, v___x_1693_);
    crate::leanh::lean_closure_set(v___f_1705_, 4, v___x_1694_);
    crate::leanh::lean_closure_set(v___f_1705_, 5, v___x_1695_);
    crate::leanh::lean_closure_set(v___f_1705_, 6, v___x_1696_);
    crate::leanh::lean_closure_set(v___f_1705_, 7, v___x_1697_);
    crate::leanh::lean_closure_set(v___f_1705_, 8, v___x_1698_);
    crate::leanh::lean_closure_set(v___f_1705_, 9, v___x_1699_);
    crate::leanh::lean_closure_set(v___f_1705_, 10, v_____do__lift_1700_);
    crate::leanh::lean_closure_set(v___f_1705_, 11, v_toPure_1701_);
    v___x_1706_ = crate::leanh::lean_apply_4(
        v_toBind_1702_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getContext_1703_,
        v___f_1705_,
    );
    return v___x_1706_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__16(
    mut v_inst_1707_: *mut crate::leanh::LeanObject,
    mut v___x_1708_: *mut crate::leanh::LeanObject,
    mut v___x_1709_: *mut crate::leanh::LeanObject,
    mut v___x_1710_: *mut crate::leanh::LeanObject,
    mut v___x_1711_: *mut crate::leanh::LeanObject,
    mut v___x_1712_: *mut crate::leanh::LeanObject,
    mut v___x_1713_: *mut crate::leanh::LeanObject,
    mut v___x_1714_: *mut crate::leanh::LeanObject,
    mut v___x_1715_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1716_: *mut crate::leanh::LeanObject,
    mut v_toPure_1717_: *mut crate::leanh::LeanObject,
    mut v_toBind_1718_: *mut crate::leanh::LeanObject,
    mut v_info_1719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getCurrMacroScope_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getContext_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getCurrMacroScope_1720_ = crate::leanh::lean_ctor_get(v_inst_1707_, 1);
    crate::leanh::lean_inc(v_getCurrMacroScope_1720_);
    v_getContext_1721_ = crate::leanh::lean_ctor_get(v_inst_1707_, 2);
    crate::leanh::lean_inc(v_getContext_1721_);
    crate::leanh::lean_dec_ref(v_inst_1707_);
    crate::leanh::lean_inc(v_toBind_1718_);
    v___f_1722_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__14 as *mut core::ffi::c_void,
        14,
        13,
    );
    crate::leanh::lean_closure_set(v___f_1722_, 0, v_info_1719_);
    crate::leanh::lean_closure_set(v___f_1722_, 1, v___x_1708_);
    crate::leanh::lean_closure_set(v___f_1722_, 2, v___x_1709_);
    crate::leanh::lean_closure_set(v___f_1722_, 3, v___x_1710_);
    crate::leanh::lean_closure_set(v___f_1722_, 4, v___x_1711_);
    crate::leanh::lean_closure_set(v___f_1722_, 5, v___x_1712_);
    crate::leanh::lean_closure_set(v___f_1722_, 6, v___x_1713_);
    crate::leanh::lean_closure_set(v___f_1722_, 7, v___x_1714_);
    crate::leanh::lean_closure_set(v___f_1722_, 8, v___x_1715_);
    crate::leanh::lean_closure_set(v___f_1722_, 9, v_____do__lift_1716_);
    crate::leanh::lean_closure_set(v___f_1722_, 10, v_toPure_1717_);
    crate::leanh::lean_closure_set(v___f_1722_, 11, v_toBind_1718_);
    crate::leanh::lean_closure_set(v___f_1722_, 12, v_getContext_1721_);
    v___x_1723_ = crate::leanh::lean_apply_4(
        v_toBind_1718_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getCurrMacroScope_1720_,
        v___f_1722_,
    );
    return v___x_1723_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__18(
    mut v_inst_1724_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1725_: *mut crate::leanh::LeanObject,
    mut v_inst_1726_: *mut crate::leanh::LeanObject,
    mut v___x_1727_: *mut crate::leanh::LeanObject,
    mut v___x_1728_: *mut crate::leanh::LeanObject,
    mut v___x_1729_: *mut crate::leanh::LeanObject,
    mut v___x_1730_: *mut crate::leanh::LeanObject,
    mut v___x_1731_: *mut crate::leanh::LeanObject,
    mut v___x_1732_: *mut crate::leanh::LeanObject,
    mut v___x_1733_: *mut crate::leanh::LeanObject,
    mut v___x_1734_: *mut crate::leanh::LeanObject,
    mut v_toBind_1735_: *mut crate::leanh::LeanObject,
    mut v___x_1736_: u8,
    mut v_____do__lift_1737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getRef_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getRef_1738_ = crate::leanh::lean_ctor_get(v_inst_1724_, 0);
    crate::leanh::lean_inc(v_getRef_1738_);
    crate::leanh::lean_dec_ref(v_inst_1724_);
    v_toPure_1739_ = crate::leanh::lean_ctor_get(v_toApplicative_1725_, 1);
    crate::leanh::lean_inc_n(v_toPure_1739_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_1725_);
    crate::leanh::lean_inc_n(v_toBind_1735_, 2);
    v___f_1740_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__16 as *mut core::ffi::c_void,
        13,
        12,
    );
    crate::leanh::lean_closure_set(v___f_1740_, 0, v_inst_1726_);
    crate::leanh::lean_closure_set(v___f_1740_, 1, v___x_1727_);
    crate::leanh::lean_closure_set(v___f_1740_, 2, v___x_1728_);
    crate::leanh::lean_closure_set(v___f_1740_, 3, v___x_1729_);
    crate::leanh::lean_closure_set(v___f_1740_, 4, v___x_1730_);
    crate::leanh::lean_closure_set(v___f_1740_, 5, v___x_1731_);
    crate::leanh::lean_closure_set(v___f_1740_, 6, v___x_1732_);
    crate::leanh::lean_closure_set(v___f_1740_, 7, v___x_1733_);
    crate::leanh::lean_closure_set(v___f_1740_, 8, v___x_1734_);
    crate::leanh::lean_closure_set(v___f_1740_, 9, v_____do__lift_1737_);
    crate::leanh::lean_closure_set(v___f_1740_, 10, v_toPure_1739_);
    crate::leanh::lean_closure_set(v___f_1740_, 11, v_toBind_1735_);
    v___x_1741_ = crate::leanh::lean_box((v___x_1736_) as usize);
    v___f_1742_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1742_, 0, v___x_1741_);
    crate::leanh::lean_closure_set(v___f_1742_, 1, v_toPure_1739_);
    v___x_1743_ = crate::leanh::lean_apply_4(
        v_toBind_1735_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRef_1738_,
        v___f_1742_,
    );
    v___x_1744_ = crate::leanh::lean_apply_4(
        v_toBind_1735_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1743_,
        v___f_1740_,
    );
    return v___x_1744_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__18___boxed(
    mut v_inst_1745_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1746_: *mut crate::leanh::LeanObject,
    mut v_inst_1747_: *mut crate::leanh::LeanObject,
    mut v___x_1748_: *mut crate::leanh::LeanObject,
    mut v___x_1749_: *mut crate::leanh::LeanObject,
    mut v___x_1750_: *mut crate::leanh::LeanObject,
    mut v___x_1751_: *mut crate::leanh::LeanObject,
    mut v___x_1752_: *mut crate::leanh::LeanObject,
    mut v___x_1753_: *mut crate::leanh::LeanObject,
    mut v___x_1754_: *mut crate::leanh::LeanObject,
    mut v___x_1755_: *mut crate::leanh::LeanObject,
    mut v_toBind_1756_: *mut crate::leanh::LeanObject,
    mut v___x_1757_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_10395__boxed_1759_: u8 = 0;
    let mut v_res_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_10395__boxed_1759_ = (crate::leanh::lean_unbox(v___x_1757_) as u8);
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
    mut v_toPure_1761_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1763_ = 0;
    v___x_1764_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1762_, v___x_1763_);
    v___x_1765_ =
        crate::leanh::lean_apply_2(v_toPure_1761_, crate::leanh::lean_box(0), v___x_1764_);
    return v___x_1765_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__22___boxed(
    mut v_toPure_1766_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1768_ =
        l_Std_Do_SPred_Notation_unpack___redArg___lam__22(v_toPure_1766_, v_____do__lift_1767_);
    crate::leanh::lean_dec(v_____do__lift_1767_);
    return v_res_1768_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__17(
    mut v_toPure_1769_: *mut crate::leanh::LeanObject,
    mut v___x_1770_: *mut crate::leanh::LeanObject,
    mut v_quotCtx_1771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1772_ =
        crate::leanh::lean_apply_2(v_toPure_1769_, crate::leanh::lean_box(0), v___x_1770_);
    return v___x_1772_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__17___boxed(
    mut v_toPure_1773_: *mut crate::leanh::LeanObject,
    mut v___x_1774_: *mut crate::leanh::LeanObject,
    mut v_quotCtx_1775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1776_ = l_Std_Do_SPred_Notation_unpack___redArg___lam__17(
        v_toPure_1773_,
        v___x_1774_,
        v_quotCtx_1775_,
    );
    crate::leanh::lean_dec(v_quotCtx_1775_);
    return v_res_1776_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__11___boxed(
    mut v_inst_1777_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_1778_: *mut crate::leanh::LeanObject,
    mut v_inst_1779_: *mut crate::leanh::LeanObject,
    mut v___x_1780_: *mut crate::leanh::LeanObject,
    mut v___x_1781_: *mut crate::leanh::LeanObject,
    mut v_toBind_1782_: *mut crate::leanh::LeanObject,
    mut v___x_1783_: *mut crate::leanh::LeanObject,
    mut v_inst_1784_: *mut crate::leanh::LeanObject,
    mut v_e_1785_: *mut crate::leanh::LeanObject,
    mut v_t_1786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_10507__boxed_1787_: u8 = 0;
    let mut v_res_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_10507__boxed_1787_ = (crate::leanh::lean_unbox(v___x_1783_) as u8);
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
    mut v_inst_1789_: *mut crate::leanh::LeanObject,
    mut v_inst_1790_: *mut crate::leanh::LeanObject,
    mut v_inst_1791_: *mut crate::leanh::LeanObject,
    mut v_x_1792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: u8 = 0;
    v___x_1793_ = l_Std_Do_termSpred_x28___x29___closed__0;
    v___x_1794_ = l_Std_Do_termSpred_x28___x29___closed__1;
    v___x_1795_ = l_Std_Do_termSpred_x28___x29___closed__3;
    crate::leanh::lean_inc(v_x_1792_);
    v___x_1796_ = l_Lean_Syntax_isOfKind(v_x_1792_, v___x_1795_);
    if v___x_1796_ == 0 {
        let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1800_: u8 = 0;
        v___x_1797_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__0;
        v___x_1798_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__1;
        v___x_1799_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__4;
        crate::leanh::lean_inc(v_x_1792_);
        v___x_1800_ = l_Lean_Syntax_isOfKind(v_x_1792_, v___x_1799_);
        if v___x_1800_ == 0 {
            let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1802_: u8 = 0;
            v___x_1801_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__8;
            crate::leanh::lean_inc(v_x_1792_);
            v___x_1802_ = l_Lean_Syntax_isOfKind(v_x_1792_, v___x_1801_);
            if v___x_1802_ == 0 {
                let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1805_: u8 = 0;
                v___x_1803_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__5;
                v___x_1804_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__6;
                crate::leanh::lean_inc(v_x_1792_);
                v___x_1805_ = l_Lean_Syntax_isOfKind(v_x_1792_, v___x_1804_);
                if v___x_1805_ == 0 {
                    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1807_: u8 = 0;
                    v___x_1806_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__10;
                    crate::leanh::lean_inc(v_x_1792_);
                    v___x_1807_ = l_Lean_Syntax_isOfKind(v_x_1792_, v___x_1806_);
                    if v___x_1807_ == 0 {
                        let mut v_toApplicative_1808_: *mut crate::leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_toBind_1809_: *mut crate::leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_getRef_1810_: *mut crate::leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_toPure_1811_: *mut crate::leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v___f_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___f_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___f_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___f_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_toApplicative_1808_ = crate::leanh::lean_ctor_get(v_inst_1789_, 0);
                        crate::leanh::lean_inc_ref(v_toApplicative_1808_);
                        v_toBind_1809_ = crate::leanh::lean_ctor_get(v_inst_1789_, 1);
                        crate::leanh::lean_inc_n(v_toBind_1809_, 4);
                        crate::leanh::lean_dec_ref(v_inst_1789_);
                        v_getRef_1810_ = crate::leanh::lean_ctor_get(v_inst_1790_, 0);
                        crate::leanh::lean_inc(v_getRef_1810_);
                        crate::leanh::lean_dec_ref(v_inst_1790_);
                        v_toPure_1811_ = crate::leanh::lean_ctor_get(v_toApplicative_1808_, 1);
                        crate::leanh::lean_inc_n(v_toPure_1811_, 2);
                        crate::leanh::lean_dec_ref(v_toApplicative_1808_);
                        v___f_1812_ = crate::leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___f_1812_, 0, v_toPure_1811_);
                        crate::leanh::lean_closure_set(v___f_1812_, 1, v_x_1792_);
                        crate::leanh::lean_inc_ref(v_inst_1791_);
                        v___f_1813_ = crate::leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        crate::leanh::lean_closure_set(v___f_1813_, 0, v_inst_1791_);
                        crate::leanh::lean_closure_set(v___f_1813_, 1, v_toBind_1809_);
                        crate::leanh::lean_closure_set(v___f_1813_, 2, v___f_1812_);
                        v___f_1814_ = crate::leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        crate::leanh::lean_closure_set(v___f_1814_, 0, v_inst_1791_);
                        crate::leanh::lean_closure_set(v___f_1814_, 1, v_toBind_1809_);
                        crate::leanh::lean_closure_set(v___f_1814_, 2, v___f_1813_);
                        v___x_1815_ = crate::leanh::lean_box((v___x_1807_) as usize);
                        v___f_1816_ = crate::leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___f_1816_, 0, v___x_1815_);
                        crate::leanh::lean_closure_set(v___f_1816_, 1, v_toPure_1811_);
                        v___x_1817_ = crate::leanh::lean_apply_4(
                            v_toBind_1809_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v_getRef_1810_,
                            v___f_1816_,
                        );
                        v___x_1818_ = crate::leanh::lean_apply_4(
                            v_toBind_1809_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_1817_,
                            v___f_1814_,
                        );
                        return v___x_1818_;
                    } else {
                        let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1822_: u8 = 0;
                        v___x_1819_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1820_ = l_Lean_Syntax_getArg(v_x_1792_, v___x_1819_);
                        v___x_1821_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12;
                        crate::leanh::lean_inc(v___x_1820_);
                        v___x_1822_ = l_Lean_Syntax_isOfKind(v___x_1820_, v___x_1821_);
                        if v___x_1822_ == 0 {
                            let mut v_toApplicative_1823_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_toBind_1824_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_getRef_1825_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_toPure_1826_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___f_1827_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___f_1828_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___f_1829_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1830_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___f_1831_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1832_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1833_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v___x_1820_);
                            v_toApplicative_1823_ = crate::leanh::lean_ctor_get(v_inst_1789_, 0);
                            crate::leanh::lean_inc_ref(v_toApplicative_1823_);
                            v_toBind_1824_ = crate::leanh::lean_ctor_get(v_inst_1789_, 1);
                            crate::leanh::lean_inc_n(v_toBind_1824_, 4);
                            crate::leanh::lean_dec_ref(v_inst_1789_);
                            v_getRef_1825_ = crate::leanh::lean_ctor_get(v_inst_1790_, 0);
                            crate::leanh::lean_inc(v_getRef_1825_);
                            crate::leanh::lean_dec_ref(v_inst_1790_);
                            v_toPure_1826_ = crate::leanh::lean_ctor_get(v_toApplicative_1823_, 1);
                            crate::leanh::lean_inc_n(v_toPure_1826_, 2);
                            crate::leanh::lean_dec_ref(v_toApplicative_1823_);
                            v___f_1827_ = crate::leanh::lean_alloc_closure(
                                l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                3,
                                2,
                            );
                            crate::leanh::lean_closure_set(v___f_1827_, 0, v_toPure_1826_);
                            crate::leanh::lean_closure_set(v___f_1827_, 1, v_x_1792_);
                            crate::leanh::lean_inc_ref(v_inst_1791_);
                            v___f_1828_ = crate::leanh::lean_alloc_closure(
                                l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed
                                    as *mut core::ffi::c_void,
                                4,
                                3,
                            );
                            crate::leanh::lean_closure_set(v___f_1828_, 0, v_inst_1791_);
                            crate::leanh::lean_closure_set(v___f_1828_, 1, v_toBind_1824_);
                            crate::leanh::lean_closure_set(v___f_1828_, 2, v___f_1827_);
                            v___f_1829_ = crate::leanh::lean_alloc_closure(
                                l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed
                                    as *mut core::ffi::c_void,
                                4,
                                3,
                            );
                            crate::leanh::lean_closure_set(v___f_1829_, 0, v_inst_1791_);
                            crate::leanh::lean_closure_set(v___f_1829_, 1, v_toBind_1824_);
                            crate::leanh::lean_closure_set(v___f_1829_, 2, v___f_1828_);
                            v___x_1830_ = crate::leanh::lean_box((v___x_1822_) as usize);
                            v___f_1831_ = crate::leanh::lean_alloc_closure(
                                l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed
                                    as *mut core::ffi::c_void,
                                3,
                                2,
                            );
                            crate::leanh::lean_closure_set(v___f_1831_, 0, v___x_1830_);
                            crate::leanh::lean_closure_set(v___f_1831_, 1, v_toPure_1826_);
                            v___x_1832_ = crate::leanh::lean_apply_4(
                                v_toBind_1824_,
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v_getRef_1825_,
                                v___f_1831_,
                            );
                            v___x_1833_ = crate::leanh::lean_apply_4(
                                v_toBind_1824_,
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_1832_,
                                v___f_1829_,
                            );
                            return v___x_1833_;
                        } else {
                            let mut v___x_1834_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1835_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1836_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1837_: u8 = 0;
                            v___x_1834_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1835_ = l_Lean_Syntax_getArg(v___x_1820_, v___x_1834_);
                            crate::leanh::lean_dec(v___x_1820_);
                            v___x_1836_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14;
                            crate::leanh::lean_inc(v___x_1835_);
                            v___x_1837_ = l_Lean_Syntax_isOfKind(v___x_1835_, v___x_1836_);
                            if v___x_1837_ == 0 {
                                let mut v_toApplicative_1838_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v_toBind_1839_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v_getRef_1840_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v_toPure_1841_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___f_1842_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___f_1843_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___f_1844_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1845_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___f_1846_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1847_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1848_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                crate::leanh::lean_dec(v___x_1835_);
                                v_toApplicative_1838_ =
                                    crate::leanh::lean_ctor_get(v_inst_1789_, 0);
                                crate::leanh::lean_inc_ref(v_toApplicative_1838_);
                                v_toBind_1839_ = crate::leanh::lean_ctor_get(v_inst_1789_, 1);
                                crate::leanh::lean_inc_n(v_toBind_1839_, 4);
                                crate::leanh::lean_dec_ref(v_inst_1789_);
                                v_getRef_1840_ = crate::leanh::lean_ctor_get(v_inst_1790_, 0);
                                crate::leanh::lean_inc(v_getRef_1840_);
                                crate::leanh::lean_dec_ref(v_inst_1790_);
                                v_toPure_1841_ =
                                    crate::leanh::lean_ctor_get(v_toApplicative_1838_, 1);
                                crate::leanh::lean_inc_n(v_toPure_1841_, 2);
                                crate::leanh::lean_dec_ref(v_toApplicative_1838_);
                                v___f_1842_ = crate::leanh::lean_alloc_closure(
                                    l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    3,
                                    2,
                                );
                                crate::leanh::lean_closure_set(v___f_1842_, 0, v_toPure_1841_);
                                crate::leanh::lean_closure_set(v___f_1842_, 1, v_x_1792_);
                                crate::leanh::lean_inc_ref(v_inst_1791_);
                                v___f_1843_ = crate::leanh::lean_alloc_closure(
                                    l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed
                                        as *mut core::ffi::c_void,
                                    4,
                                    3,
                                );
                                crate::leanh::lean_closure_set(v___f_1843_, 0, v_inst_1791_);
                                crate::leanh::lean_closure_set(v___f_1843_, 1, v_toBind_1839_);
                                crate::leanh::lean_closure_set(v___f_1843_, 2, v___f_1842_);
                                v___f_1844_ = crate::leanh::lean_alloc_closure(
                                    l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed
                                        as *mut core::ffi::c_void,
                                    4,
                                    3,
                                );
                                crate::leanh::lean_closure_set(v___f_1844_, 0, v_inst_1791_);
                                crate::leanh::lean_closure_set(v___f_1844_, 1, v_toBind_1839_);
                                crate::leanh::lean_closure_set(v___f_1844_, 2, v___f_1843_);
                                v___x_1845_ = crate::leanh::lean_box((v___x_1837_) as usize);
                                v___f_1846_ = crate::leanh::lean_alloc_closure(
                                    l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed
                                        as *mut core::ffi::c_void,
                                    3,
                                    2,
                                );
                                crate::leanh::lean_closure_set(v___f_1846_, 0, v___x_1845_);
                                crate::leanh::lean_closure_set(v___f_1846_, 1, v_toPure_1841_);
                                v___x_1847_ = crate::leanh::lean_apply_4(
                                    v_toBind_1839_,
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v_getRef_1840_,
                                    v___f_1846_,
                                );
                                v___x_1848_ = crate::leanh::lean_apply_4(
                                    v_toBind_1839_,
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_1847_,
                                    v___f_1844_,
                                );
                                return v___x_1848_;
                            } else {
                                let mut v___x_1849_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1850_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1851_: u8 = 0;
                                v___x_1849_ = l_Lean_Syntax_getArg(v___x_1835_, v___x_1819_);
                                crate::leanh::lean_dec(v___x_1835_);
                                v___x_1850_ = crate::leanh::lean_box(0);
                                v___x_1851_ = l_Lean_Syntax_matchesIdent(v___x_1849_, v___x_1850_);
                                crate::leanh::lean_dec(v___x_1849_);
                                if v___x_1851_ == 0 {
                                    let mut v_toApplicative_1852_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v_toBind_1853_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v_getRef_1854_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v_toPure_1855_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___f_1856_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___f_1857_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___f_1858_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1859_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___f_1860_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1861_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1862_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    v_toApplicative_1852_ =
                                        crate::leanh::lean_ctor_get(v_inst_1789_, 0);
                                    crate::leanh::lean_inc_ref(v_toApplicative_1852_);
                                    v_toBind_1853_ = crate::leanh::lean_ctor_get(v_inst_1789_, 1);
                                    crate::leanh::lean_inc_n(v_toBind_1853_, 4);
                                    crate::leanh::lean_dec_ref(v_inst_1789_);
                                    v_getRef_1854_ = crate::leanh::lean_ctor_get(v_inst_1790_, 0);
                                    crate::leanh::lean_inc(v_getRef_1854_);
                                    crate::leanh::lean_dec_ref(v_inst_1790_);
                                    v_toPure_1855_ =
                                        crate::leanh::lean_ctor_get(v_toApplicative_1852_, 1);
                                    crate::leanh::lean_inc_n(v_toPure_1855_, 2);
                                    crate::leanh::lean_dec_ref(v_toApplicative_1852_);
                                    v___f_1856_ = crate::leanh::lean_alloc_closure(
                                        l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed
                                            as *mut core::ffi::c_void,
                                        3,
                                        2,
                                    );
                                    crate::leanh::lean_closure_set(v___f_1856_, 0, v_toPure_1855_);
                                    crate::leanh::lean_closure_set(v___f_1856_, 1, v_x_1792_);
                                    crate::leanh::lean_inc_ref(v_inst_1791_);
                                    v___f_1857_ = crate::leanh::lean_alloc_closure(
                                        l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed
                                            as *mut core::ffi::c_void,
                                        4,
                                        3,
                                    );
                                    crate::leanh::lean_closure_set(v___f_1857_, 0, v_inst_1791_);
                                    crate::leanh::lean_closure_set(v___f_1857_, 1, v_toBind_1853_);
                                    crate::leanh::lean_closure_set(v___f_1857_, 2, v___f_1856_);
                                    v___f_1858_ = crate::leanh::lean_alloc_closure(
                                        l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed
                                            as *mut core::ffi::c_void,
                                        4,
                                        3,
                                    );
                                    crate::leanh::lean_closure_set(v___f_1858_, 0, v_inst_1791_);
                                    crate::leanh::lean_closure_set(v___f_1858_, 1, v_toBind_1853_);
                                    crate::leanh::lean_closure_set(v___f_1858_, 2, v___f_1857_);
                                    v___x_1859_ = crate::leanh::lean_box((v___x_1851_) as usize);
                                    v___f_1860_ = crate::leanh::lean_alloc_closure(
                                        l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed
                                            as *mut core::ffi::c_void,
                                        3,
                                        2,
                                    );
                                    crate::leanh::lean_closure_set(v___f_1860_, 0, v___x_1859_);
                                    crate::leanh::lean_closure_set(v___f_1860_, 1, v_toPure_1855_);
                                    v___x_1861_ = crate::leanh::lean_apply_4(
                                        v_toBind_1853_,
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        v_getRef_1854_,
                                        v___f_1860_,
                                    );
                                    v___x_1862_ = crate::leanh::lean_apply_4(
                                        v_toBind_1853_,
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        v___x_1861_,
                                        v___f_1858_,
                                    );
                                    return v___x_1862_;
                                } else {
                                    let mut v___x_1863_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1864_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1865_: u8 = 0;
                                    v___x_1863_ = crate::leanh::lean_unsigned_to_nat(3);
                                    v___x_1864_ = l_Lean_Syntax_getArg(v_x_1792_, v___x_1863_);
                                    crate::leanh::lean_inc(v___x_1864_);
                                    v___x_1865_ =
                                        l_Lean_Syntax_matchesNull(v___x_1864_, v___x_1834_);
                                    if v___x_1865_ == 0 {
                                        let mut v_toApplicative_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                        let mut v_toBind_1867_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v_getRef_1868_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v_toPure_1869_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___f_1870_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___f_1871_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___f_1872_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1873_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___f_1874_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1875_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1876_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        crate::leanh::lean_dec(v___x_1864_);
                                        v_toApplicative_1866_ =
                                            crate::leanh::lean_ctor_get(v_inst_1789_, 0);
                                        crate::leanh::lean_inc_ref(v_toApplicative_1866_);
                                        v_toBind_1867_ =
                                            crate::leanh::lean_ctor_get(v_inst_1789_, 1);
                                        crate::leanh::lean_inc_n(v_toBind_1867_, 4);
                                        crate::leanh::lean_dec_ref(v_inst_1789_);
                                        v_getRef_1868_ =
                                            crate::leanh::lean_ctor_get(v_inst_1790_, 0);
                                        crate::leanh::lean_inc(v_getRef_1868_);
                                        crate::leanh::lean_dec_ref(v_inst_1790_);
                                        v_toPure_1869_ =
                                            crate::leanh::lean_ctor_get(v_toApplicative_1866_, 1);
                                        crate::leanh::lean_inc_n(v_toPure_1869_, 2);
                                        crate::leanh::lean_dec_ref(v_toApplicative_1866_);
                                        v___f_1870_ = crate::leanh::lean_alloc_closure(
                                            l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed
                                                as *mut core::ffi::c_void,
                                            3,
                                            2,
                                        );
                                        crate::leanh::lean_closure_set(
                                            v___f_1870_,
                                            0,
                                            v_toPure_1869_,
                                        );
                                        crate::leanh::lean_closure_set(v___f_1870_, 1, v_x_1792_);
                                        crate::leanh::lean_inc_ref(v_inst_1791_);
                                        v___f_1871_ = crate::leanh::lean_alloc_closure(
                                            l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed
                                                as *mut core::ffi::c_void,
                                            4,
                                            3,
                                        );
                                        crate::leanh::lean_closure_set(
                                            v___f_1871_,
                                            0,
                                            v_inst_1791_,
                                        );
                                        crate::leanh::lean_closure_set(
                                            v___f_1871_,
                                            1,
                                            v_toBind_1867_,
                                        );
                                        crate::leanh::lean_closure_set(v___f_1871_, 2, v___f_1870_);
                                        v___f_1872_ = crate::leanh::lean_alloc_closure(
                                            l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed
                                                as *mut core::ffi::c_void,
                                            4,
                                            3,
                                        );
                                        crate::leanh::lean_closure_set(
                                            v___f_1872_,
                                            0,
                                            v_inst_1791_,
                                        );
                                        crate::leanh::lean_closure_set(
                                            v___f_1872_,
                                            1,
                                            v_toBind_1867_,
                                        );
                                        crate::leanh::lean_closure_set(v___f_1872_, 2, v___f_1871_);
                                        v___x_1873_ =
                                            crate::leanh::lean_box((v___x_1865_) as usize);
                                        v___f_1874_ = crate::leanh::lean_alloc_closure(
                                            l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed
                                                as *mut core::ffi::c_void,
                                            3,
                                            2,
                                        );
                                        crate::leanh::lean_closure_set(v___f_1874_, 0, v___x_1873_);
                                        crate::leanh::lean_closure_set(
                                            v___f_1874_,
                                            1,
                                            v_toPure_1869_,
                                        );
                                        v___x_1875_ = crate::leanh::lean_apply_4(
                                            v_toBind_1867_,
                                            crate::leanh::lean_box(0),
                                            crate::leanh::lean_box(0),
                                            v_getRef_1868_,
                                            v___f_1874_,
                                        );
                                        v___x_1876_ = crate::leanh::lean_apply_4(
                                            v_toBind_1867_,
                                            crate::leanh::lean_box(0),
                                            crate::leanh::lean_box(0),
                                            v___x_1875_,
                                            v___f_1872_,
                                        );
                                        return v___x_1876_;
                                    } else {
                                        let mut v_toApplicative_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                        let mut v_toBind_1878_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v_P_1879_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1880_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1881_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___f_1882_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1883_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1884_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        v_toApplicative_1877_ =
                                            crate::leanh::lean_ctor_get(v_inst_1789_, 0);
                                        v_toBind_1878_ =
                                            crate::leanh::lean_ctor_get(v_inst_1789_, 1);
                                        crate::leanh::lean_inc_n(v_toBind_1878_, 2);
                                        v_P_1879_ = l_Lean_Syntax_getArg(v_x_1792_, v___x_1834_);
                                        crate::leanh::lean_dec(v_x_1792_);
                                        v___x_1880_ =
                                            l_Lean_Syntax_getArg(v___x_1864_, v___x_1819_);
                                        crate::leanh::lean_dec(v___x_1864_);
                                        v___x_1881_ =
                                            crate::leanh::lean_box((v___x_1805_) as usize);
                                        crate::leanh::lean_inc_ref(v_inst_1791_);
                                        crate::leanh::lean_inc_ref(v_toApplicative_1877_);
                                        crate::leanh::lean_inc_ref(v_inst_1790_);
                                        v___f_1882_ = crate::leanh::lean_alloc_closure(
                                            l_Std_Do_SPred_Notation_unpack___redArg___lam__7___boxed
                                                as *mut core::ffi::c_void,
                                            15,
                                            14,
                                        );
                                        crate::leanh::lean_closure_set(
                                            v___f_1882_,
                                            0,
                                            v_inst_1790_,
                                        );
                                        crate::leanh::lean_closure_set(
                                            v___f_1882_,
                                            1,
                                            v_toApplicative_1877_,
                                        );
                                        crate::leanh::lean_closure_set(
                                            v___f_1882_,
                                            2,
                                            v_inst_1791_,
                                        );
                                        crate::leanh::lean_closure_set(v___f_1882_, 3, v___x_1850_);
                                        crate::leanh::lean_closure_set(v___f_1882_, 4, v___x_1793_);
                                        crate::leanh::lean_closure_set(v___f_1882_, 5, v___x_1794_);
                                        crate::leanh::lean_closure_set(v___f_1882_, 6, v___x_1797_);
                                        crate::leanh::lean_closure_set(v___f_1882_, 7, v___x_1798_);
                                        crate::leanh::lean_closure_set(v___f_1882_, 8, v___x_1836_);
                                        crate::leanh::lean_closure_set(v___f_1882_, 9, v___x_1821_);
                                        crate::leanh::lean_closure_set(
                                            v___f_1882_,
                                            10,
                                            v___x_1880_,
                                        );
                                        crate::leanh::lean_closure_set(
                                            v___f_1882_,
                                            11,
                                            v___x_1806_,
                                        );
                                        crate::leanh::lean_closure_set(
                                            v___f_1882_,
                                            12,
                                            v_toBind_1878_,
                                        );
                                        crate::leanh::lean_closure_set(
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
                                        v___x_1884_ = crate::leanh::lean_apply_4(
                                            v_toBind_1878_,
                                            crate::leanh::lean_box(0),
                                            crate::leanh::lean_box(0),
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
                    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1888_: u8 = 0;
                    v___x_1885_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1886_ = l_Lean_Syntax_getArg(v_x_1792_, v___x_1885_);
                    v___x_1887_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__42;
                    crate::leanh::lean_inc(v___x_1886_);
                    v___x_1888_ = l_Lean_Syntax_isOfKind(v___x_1886_, v___x_1887_);
                    if v___x_1888_ == 0 {
                        let mut v_toApplicative_1889_: *mut crate::leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_toBind_1890_: *mut crate::leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_getRef_1891_: *mut crate::leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_toPure_1892_: *mut crate::leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v___f_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___f_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___f_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___f_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v___x_1886_);
                        v_toApplicative_1889_ = crate::leanh::lean_ctor_get(v_inst_1789_, 0);
                        crate::leanh::lean_inc_ref(v_toApplicative_1889_);
                        v_toBind_1890_ = crate::leanh::lean_ctor_get(v_inst_1789_, 1);
                        crate::leanh::lean_inc_n(v_toBind_1890_, 4);
                        crate::leanh::lean_dec_ref(v_inst_1789_);
                        v_getRef_1891_ = crate::leanh::lean_ctor_get(v_inst_1790_, 0);
                        crate::leanh::lean_inc(v_getRef_1891_);
                        crate::leanh::lean_dec_ref(v_inst_1790_);
                        v_toPure_1892_ = crate::leanh::lean_ctor_get(v_toApplicative_1889_, 1);
                        crate::leanh::lean_inc_n(v_toPure_1892_, 2);
                        crate::leanh::lean_dec_ref(v_toApplicative_1889_);
                        v___f_1893_ = crate::leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___f_1893_, 0, v_toPure_1892_);
                        crate::leanh::lean_closure_set(v___f_1893_, 1, v_x_1792_);
                        crate::leanh::lean_inc_ref(v_inst_1791_);
                        v___f_1894_ = crate::leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        crate::leanh::lean_closure_set(v___f_1894_, 0, v_inst_1791_);
                        crate::leanh::lean_closure_set(v___f_1894_, 1, v_toBind_1890_);
                        crate::leanh::lean_closure_set(v___f_1894_, 2, v___f_1893_);
                        v___f_1895_ = crate::leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        crate::leanh::lean_closure_set(v___f_1895_, 0, v_inst_1791_);
                        crate::leanh::lean_closure_set(v___f_1895_, 1, v_toBind_1890_);
                        crate::leanh::lean_closure_set(v___f_1895_, 2, v___f_1894_);
                        v___x_1896_ = crate::leanh::lean_box((v___x_1888_) as usize);
                        v___f_1897_ = crate::leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___f_1897_, 0, v___x_1896_);
                        crate::leanh::lean_closure_set(v___f_1897_, 1, v_toPure_1892_);
                        v___x_1898_ = crate::leanh::lean_apply_4(
                            v_toBind_1890_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v_getRef_1891_,
                            v___f_1897_,
                        );
                        v___x_1899_ = crate::leanh::lean_apply_4(
                            v_toBind_1890_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_1898_,
                            v___f_1895_,
                        );
                        return v___x_1899_;
                    } else {
                        let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1902_: u8 = 0;
                        v___x_1900_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1901_ = l_Lean_Syntax_getArg(v___x_1886_, v___x_1885_);
                        v___x_1902_ = l_Lean_Syntax_matchesNull(v___x_1901_, v___x_1900_);
                        if v___x_1902_ == 0 {
                            let mut v_toApplicative_1903_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_toBind_1904_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_getRef_1905_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_toPure_1906_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___f_1907_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___f_1908_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___f_1909_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1910_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___f_1911_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1912_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1913_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v___x_1886_);
                            v_toApplicative_1903_ = crate::leanh::lean_ctor_get(v_inst_1789_, 0);
                            crate::leanh::lean_inc_ref(v_toApplicative_1903_);
                            v_toBind_1904_ = crate::leanh::lean_ctor_get(v_inst_1789_, 1);
                            crate::leanh::lean_inc_n(v_toBind_1904_, 4);
                            crate::leanh::lean_dec_ref(v_inst_1789_);
                            v_getRef_1905_ = crate::leanh::lean_ctor_get(v_inst_1790_, 0);
                            crate::leanh::lean_inc(v_getRef_1905_);
                            crate::leanh::lean_dec_ref(v_inst_1790_);
                            v_toPure_1906_ = crate::leanh::lean_ctor_get(v_toApplicative_1903_, 1);
                            crate::leanh::lean_inc_n(v_toPure_1906_, 2);
                            crate::leanh::lean_dec_ref(v_toApplicative_1903_);
                            v___f_1907_ = crate::leanh::lean_alloc_closure(
                                l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                3,
                                2,
                            );
                            crate::leanh::lean_closure_set(v___f_1907_, 0, v_toPure_1906_);
                            crate::leanh::lean_closure_set(v___f_1907_, 1, v_x_1792_);
                            crate::leanh::lean_inc_ref(v_inst_1791_);
                            v___f_1908_ = crate::leanh::lean_alloc_closure(
                                l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed
                                    as *mut core::ffi::c_void,
                                4,
                                3,
                            );
                            crate::leanh::lean_closure_set(v___f_1908_, 0, v_inst_1791_);
                            crate::leanh::lean_closure_set(v___f_1908_, 1, v_toBind_1904_);
                            crate::leanh::lean_closure_set(v___f_1908_, 2, v___f_1907_);
                            v___f_1909_ = crate::leanh::lean_alloc_closure(
                                l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed
                                    as *mut core::ffi::c_void,
                                4,
                                3,
                            );
                            crate::leanh::lean_closure_set(v___f_1909_, 0, v_inst_1791_);
                            crate::leanh::lean_closure_set(v___f_1909_, 1, v_toBind_1904_);
                            crate::leanh::lean_closure_set(v___f_1909_, 2, v___f_1908_);
                            v___x_1910_ = crate::leanh::lean_box((v___x_1902_) as usize);
                            v___f_1911_ = crate::leanh::lean_alloc_closure(
                                l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed
                                    as *mut core::ffi::c_void,
                                3,
                                2,
                            );
                            crate::leanh::lean_closure_set(v___f_1911_, 0, v___x_1910_);
                            crate::leanh::lean_closure_set(v___f_1911_, 1, v_toPure_1906_);
                            v___x_1912_ = crate::leanh::lean_apply_4(
                                v_toBind_1904_,
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v_getRef_1905_,
                                v___f_1911_,
                            );
                            v___x_1913_ = crate::leanh::lean_apply_4(
                                v_toBind_1904_,
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_1912_,
                                v___f_1909_,
                            );
                            return v___x_1913_;
                        } else {
                            let mut v_toApplicative_1914_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_toBind_1915_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1916_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1917_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_b_1918_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_xs_1919_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1920_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___f_1921_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1922_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1923_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v_x_1792_);
                            v_toApplicative_1914_ = crate::leanh::lean_ctor_get(v_inst_1789_, 0);
                            v_toBind_1915_ = crate::leanh::lean_ctor_get(v_inst_1789_, 1);
                            crate::leanh::lean_inc_n(v_toBind_1915_, 2);
                            v___x_1916_ = l_Lean_Syntax_getArg(v___x_1886_, v___x_1900_);
                            v___x_1917_ = crate::leanh::lean_unsigned_to_nat(3);
                            v_b_1918_ = l_Lean_Syntax_getArg(v___x_1886_, v___x_1917_);
                            crate::leanh::lean_dec(v___x_1886_);
                            v_xs_1919_ = l_Lean_Syntax_getArgs(v___x_1916_);
                            crate::leanh::lean_dec(v___x_1916_);
                            v___x_1920_ = crate::leanh::lean_box((v___x_1802_) as usize);
                            crate::leanh::lean_inc_ref(v_inst_1791_);
                            crate::leanh::lean_inc_ref(v_toApplicative_1914_);
                            crate::leanh::lean_inc_ref(v_inst_1790_);
                            v___f_1921_ = crate::leanh::lean_alloc_closure(
                                l_Std_Do_SPred_Notation_unpack___redArg___lam__10___boxed
                                    as *mut core::ffi::c_void,
                                10,
                                9,
                            );
                            crate::leanh::lean_closure_set(v___f_1921_, 0, v_inst_1790_);
                            crate::leanh::lean_closure_set(v___f_1921_, 1, v_toApplicative_1914_);
                            crate::leanh::lean_closure_set(v___f_1921_, 2, v_inst_1791_);
                            crate::leanh::lean_closure_set(v___f_1921_, 3, v___x_1803_);
                            crate::leanh::lean_closure_set(v___f_1921_, 4, v_xs_1919_);
                            crate::leanh::lean_closure_set(v___f_1921_, 5, v___x_1887_);
                            crate::leanh::lean_closure_set(v___f_1921_, 6, v___x_1804_);
                            crate::leanh::lean_closure_set(v___f_1921_, 7, v_toBind_1915_);
                            crate::leanh::lean_closure_set(v___f_1921_, 8, v___x_1920_);
                            v___x_1922_ = l_Std_Do_SPred_Notation_unpack___redArg(
                                v_inst_1789_,
                                v_inst_1790_,
                                v_inst_1791_,
                                v_b_1918_,
                            );
                            v___x_1923_ = crate::leanh::lean_apply_4(
                                v_toBind_1915_,
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_1922_,
                                v___f_1921_,
                            );
                            return v___x_1923_;
                        }
                    }
                }
            } else {
                let mut v_toApplicative_1924_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toBind_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_t_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_e_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_toApplicative_1924_ = crate::leanh::lean_ctor_get(v_inst_1789_, 0);
                v_toBind_1925_ = crate::leanh::lean_ctor_get(v_inst_1789_, 1);
                crate::leanh::lean_inc_n(v_toBind_1925_, 2);
                v___x_1926_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1927_ = l_Lean_Syntax_getArg(v_x_1792_, v___x_1926_);
                v___x_1928_ = crate::leanh::lean_unsigned_to_nat(3);
                v_t_1929_ = l_Lean_Syntax_getArg(v_x_1792_, v___x_1928_);
                v___x_1930_ = crate::leanh::lean_unsigned_to_nat(5);
                v_e_1931_ = l_Lean_Syntax_getArg(v_x_1792_, v___x_1930_);
                crate::leanh::lean_dec(v_x_1792_);
                v___x_1932_ = crate::leanh::lean_box((v___x_1800_) as usize);
                crate::leanh::lean_inc_ref(v_inst_1789_);
                crate::leanh::lean_inc_ref(v_inst_1791_);
                crate::leanh::lean_inc_ref(v_toApplicative_1924_);
                crate::leanh::lean_inc_ref(v_inst_1790_);
                v___f_1933_ = crate::leanh::lean_alloc_closure(
                    l_Std_Do_SPred_Notation_unpack___redArg___lam__11___boxed
                        as *mut core::ffi::c_void,
                    10,
                    9,
                );
                crate::leanh::lean_closure_set(v___f_1933_, 0, v_inst_1790_);
                crate::leanh::lean_closure_set(v___f_1933_, 1, v_toApplicative_1924_);
                crate::leanh::lean_closure_set(v___f_1933_, 2, v_inst_1791_);
                crate::leanh::lean_closure_set(v___f_1933_, 3, v___x_1801_);
                crate::leanh::lean_closure_set(v___f_1933_, 4, v___x_1927_);
                crate::leanh::lean_closure_set(v___f_1933_, 5, v_toBind_1925_);
                crate::leanh::lean_closure_set(v___f_1933_, 6, v___x_1932_);
                crate::leanh::lean_closure_set(v___f_1933_, 7, v_inst_1789_);
                crate::leanh::lean_closure_set(v___f_1933_, 8, v_e_1931_);
                v___x_1934_ = l_Std_Do_SPred_Notation_unpack___redArg(
                    v_inst_1789_,
                    v_inst_1790_,
                    v_inst_1791_,
                    v_t_1929_,
                );
                v___x_1935_ = crate::leanh::lean_apply_4(
                    v_toBind_1925_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1934_,
                    v___f_1933_,
                );
                return v___x_1935_;
            }
        } else {
            let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1939_: u8 = 0;
            v___x_1936_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_1937_ = l_Lean_Syntax_getArg(v_x_1792_, v___x_1936_);
            v___x_1938_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__12;
            crate::leanh::lean_inc(v___x_1937_);
            v___x_1939_ = l_Lean_Syntax_isOfKind(v___x_1937_, v___x_1938_);
            if v___x_1939_ == 0 {
                let mut v_toApplicative_1940_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toBind_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_getRef_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_toPure_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_1937_);
                v_toApplicative_1940_ = crate::leanh::lean_ctor_get(v_inst_1789_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_1940_);
                v_toBind_1941_ = crate::leanh::lean_ctor_get(v_inst_1789_, 1);
                crate::leanh::lean_inc_n(v_toBind_1941_, 4);
                crate::leanh::lean_dec_ref(v_inst_1789_);
                v_getRef_1942_ = crate::leanh::lean_ctor_get(v_inst_1790_, 0);
                crate::leanh::lean_inc(v_getRef_1942_);
                crate::leanh::lean_dec_ref(v_inst_1790_);
                v_toPure_1943_ = crate::leanh::lean_ctor_get(v_toApplicative_1940_, 1);
                crate::leanh::lean_inc_n(v_toPure_1943_, 2);
                crate::leanh::lean_dec_ref(v_toApplicative_1940_);
                v___f_1944_ = crate::leanh::lean_alloc_closure(
                    l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1944_, 0, v_toPure_1943_);
                crate::leanh::lean_closure_set(v___f_1944_, 1, v_x_1792_);
                crate::leanh::lean_inc_ref(v_inst_1791_);
                v___f_1945_ = crate::leanh::lean_alloc_closure(
                    l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_1945_, 0, v_inst_1791_);
                crate::leanh::lean_closure_set(v___f_1945_, 1, v_toBind_1941_);
                crate::leanh::lean_closure_set(v___f_1945_, 2, v___f_1944_);
                v___f_1946_ = crate::leanh::lean_alloc_closure(
                    l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_1946_, 0, v_inst_1791_);
                crate::leanh::lean_closure_set(v___f_1946_, 1, v_toBind_1941_);
                crate::leanh::lean_closure_set(v___f_1946_, 2, v___f_1945_);
                v___x_1947_ = crate::leanh::lean_box((v___x_1939_) as usize);
                v___f_1948_ = crate::leanh::lean_alloc_closure(
                    l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1948_, 0, v___x_1947_);
                crate::leanh::lean_closure_set(v___f_1948_, 1, v_toPure_1943_);
                v___x_1949_ = crate::leanh::lean_apply_4(
                    v_toBind_1941_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_getRef_1942_,
                    v___f_1948_,
                );
                v___x_1950_ = crate::leanh::lean_apply_4(
                    v_toBind_1941_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1949_,
                    v___f_1946_,
                );
                return v___x_1950_;
            } else {
                let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1954_: u8 = 0;
                v___x_1951_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1952_ = l_Lean_Syntax_getArg(v___x_1937_, v___x_1951_);
                crate::leanh::lean_dec(v___x_1937_);
                v___x_1953_ = l_Std_Do___aux__Std__Do__SPred__Notation__Basic______macroRules__Std__Do__termSpred_x28___x29__2___closed__14;
                crate::leanh::lean_inc(v___x_1952_);
                v___x_1954_ = l_Lean_Syntax_isOfKind(v___x_1952_, v___x_1953_);
                if v___x_1954_ == 0 {
                    let mut v_toApplicative_1955_: *mut crate::leanh::LeanObject =
                        core::ptr::null_mut();
                    let mut v_toBind_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_getRef_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_toPure_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___f_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___f_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___f_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___f_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_1952_);
                    v_toApplicative_1955_ = crate::leanh::lean_ctor_get(v_inst_1789_, 0);
                    crate::leanh::lean_inc_ref(v_toApplicative_1955_);
                    v_toBind_1956_ = crate::leanh::lean_ctor_get(v_inst_1789_, 1);
                    crate::leanh::lean_inc_n(v_toBind_1956_, 4);
                    crate::leanh::lean_dec_ref(v_inst_1789_);
                    v_getRef_1957_ = crate::leanh::lean_ctor_get(v_inst_1790_, 0);
                    crate::leanh::lean_inc(v_getRef_1957_);
                    crate::leanh::lean_dec_ref(v_inst_1790_);
                    v_toPure_1958_ = crate::leanh::lean_ctor_get(v_toApplicative_1955_, 1);
                    crate::leanh::lean_inc_n(v_toPure_1958_, 2);
                    crate::leanh::lean_dec_ref(v_toApplicative_1955_);
                    v___f_1959_ = crate::leanh::lean_alloc_closure(
                        l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_1959_, 0, v_toPure_1958_);
                    crate::leanh::lean_closure_set(v___f_1959_, 1, v_x_1792_);
                    crate::leanh::lean_inc_ref(v_inst_1791_);
                    v___f_1960_ = crate::leanh::lean_alloc_closure(
                        l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___f_1960_, 0, v_inst_1791_);
                    crate::leanh::lean_closure_set(v___f_1960_, 1, v_toBind_1956_);
                    crate::leanh::lean_closure_set(v___f_1960_, 2, v___f_1959_);
                    v___f_1961_ = crate::leanh::lean_alloc_closure(
                        l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___f_1961_, 0, v_inst_1791_);
                    crate::leanh::lean_closure_set(v___f_1961_, 1, v_toBind_1956_);
                    crate::leanh::lean_closure_set(v___f_1961_, 2, v___f_1960_);
                    v___x_1962_ = crate::leanh::lean_box((v___x_1954_) as usize);
                    v___f_1963_ = crate::leanh::lean_alloc_closure(
                        l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_1963_, 0, v___x_1962_);
                    crate::leanh::lean_closure_set(v___f_1963_, 1, v_toPure_1958_);
                    v___x_1964_ = crate::leanh::lean_apply_4(
                        v_toBind_1956_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v_getRef_1957_,
                        v___f_1963_,
                    );
                    v___x_1965_ = crate::leanh::lean_apply_4(
                        v_toBind_1956_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_1964_,
                        v___f_1961_,
                    );
                    return v___x_1965_;
                } else {
                    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1968_: u8 = 0;
                    v___x_1966_ = l_Lean_Syntax_getArg(v___x_1952_, v___x_1936_);
                    crate::leanh::lean_dec(v___x_1952_);
                    v___x_1967_ = crate::leanh::lean_box(0);
                    v___x_1968_ = l_Lean_Syntax_matchesIdent(v___x_1966_, v___x_1967_);
                    crate::leanh::lean_dec(v___x_1966_);
                    if v___x_1968_ == 0 {
                        let mut v_toApplicative_1969_: *mut crate::leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_toBind_1970_: *mut crate::leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_getRef_1971_: *mut crate::leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_toPure_1972_: *mut crate::leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v___f_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___f_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___f_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___f_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_toApplicative_1969_ = crate::leanh::lean_ctor_get(v_inst_1789_, 0);
                        crate::leanh::lean_inc_ref(v_toApplicative_1969_);
                        v_toBind_1970_ = crate::leanh::lean_ctor_get(v_inst_1789_, 1);
                        crate::leanh::lean_inc_n(v_toBind_1970_, 4);
                        crate::leanh::lean_dec_ref(v_inst_1789_);
                        v_getRef_1971_ = crate::leanh::lean_ctor_get(v_inst_1790_, 0);
                        crate::leanh::lean_inc(v_getRef_1971_);
                        crate::leanh::lean_dec_ref(v_inst_1790_);
                        v_toPure_1972_ = crate::leanh::lean_ctor_get(v_toApplicative_1969_, 1);
                        crate::leanh::lean_inc_n(v_toPure_1972_, 2);
                        crate::leanh::lean_dec_ref(v_toApplicative_1969_);
                        v___f_1973_ = crate::leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__0___boxed
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___f_1973_, 0, v_toPure_1972_);
                        crate::leanh::lean_closure_set(v___f_1973_, 1, v_x_1792_);
                        crate::leanh::lean_inc_ref(v_inst_1791_);
                        v___f_1974_ = crate::leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        crate::leanh::lean_closure_set(v___f_1974_, 0, v_inst_1791_);
                        crate::leanh::lean_closure_set(v___f_1974_, 1, v_toBind_1970_);
                        crate::leanh::lean_closure_set(v___f_1974_, 2, v___f_1973_);
                        v___f_1975_ = crate::leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        crate::leanh::lean_closure_set(v___f_1975_, 0, v_inst_1791_);
                        crate::leanh::lean_closure_set(v___f_1975_, 1, v_toBind_1970_);
                        crate::leanh::lean_closure_set(v___f_1975_, 2, v___f_1974_);
                        v___x_1976_ = crate::leanh::lean_box((v___x_1968_) as usize);
                        v___f_1977_ = crate::leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__3___boxed
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___f_1977_, 0, v___x_1976_);
                        crate::leanh::lean_closure_set(v___f_1977_, 1, v_toPure_1972_);
                        v___x_1978_ = crate::leanh::lean_apply_4(
                            v_toBind_1970_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v_getRef_1971_,
                            v___f_1977_,
                        );
                        v___x_1979_ = crate::leanh::lean_apply_4(
                            v_toBind_1970_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_1978_,
                            v___f_1975_,
                        );
                        return v___x_1979_;
                    } else {
                        let mut v_toApplicative_1980_: *mut crate::leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_toBind_1981_: *mut crate::leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_P_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___f_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_toApplicative_1980_ = crate::leanh::lean_ctor_get(v_inst_1789_, 0);
                        v_toBind_1981_ = crate::leanh::lean_ctor_get(v_inst_1789_, 1);
                        crate::leanh::lean_inc_n(v_toBind_1981_, 2);
                        v_P_1982_ = l_Lean_Syntax_getArg(v_x_1792_, v___x_1951_);
                        crate::leanh::lean_dec(v_x_1792_);
                        v___x_1983_ = crate::leanh::lean_box((v___x_1796_) as usize);
                        crate::leanh::lean_inc_ref(v_inst_1791_);
                        crate::leanh::lean_inc_ref(v_toApplicative_1980_);
                        crate::leanh::lean_inc_ref(v_inst_1790_);
                        v___f_1984_ = crate::leanh::lean_alloc_closure(
                            l_Std_Do_SPred_Notation_unpack___redArg___lam__18___boxed
                                as *mut core::ffi::c_void,
                            14,
                            13,
                        );
                        crate::leanh::lean_closure_set(v___f_1984_, 0, v_inst_1790_);
                        crate::leanh::lean_closure_set(v___f_1984_, 1, v_toApplicative_1980_);
                        crate::leanh::lean_closure_set(v___f_1984_, 2, v_inst_1791_);
                        crate::leanh::lean_closure_set(v___f_1984_, 3, v___x_1967_);
                        crate::leanh::lean_closure_set(v___f_1984_, 4, v___x_1793_);
                        crate::leanh::lean_closure_set(v___f_1984_, 5, v___x_1794_);
                        crate::leanh::lean_closure_set(v___f_1984_, 6, v___x_1797_);
                        crate::leanh::lean_closure_set(v___f_1984_, 7, v___x_1798_);
                        crate::leanh::lean_closure_set(v___f_1984_, 8, v___x_1953_);
                        crate::leanh::lean_closure_set(v___f_1984_, 9, v___x_1938_);
                        crate::leanh::lean_closure_set(v___f_1984_, 10, v___x_1799_);
                        crate::leanh::lean_closure_set(v___f_1984_, 11, v_toBind_1981_);
                        crate::leanh::lean_closure_set(v___f_1984_, 12, v___x_1983_);
                        v___x_1985_ = l_Std_Do_SPred_Notation_unpack___redArg(
                            v_inst_1789_,
                            v_inst_1790_,
                            v_inst_1791_,
                            v_P_1982_,
                        );
                        v___x_1986_ = crate::leanh::lean_apply_4(
                            v_toBind_1981_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_1985_,
                            v___f_1984_,
                        );
                        return v___x_1986_;
                    }
                }
            }
        }
    } else {
        let mut v_toApplicative_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_getRef_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1987_ = crate::leanh::lean_ctor_get(v_inst_1789_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1987_);
        v_toBind_1988_ = crate::leanh::lean_ctor_get(v_inst_1789_, 1);
        crate::leanh::lean_inc_n(v_toBind_1988_, 4);
        crate::leanh::lean_dec_ref(v_inst_1789_);
        v_getRef_1989_ = crate::leanh::lean_ctor_get(v_inst_1790_, 0);
        crate::leanh::lean_inc(v_getRef_1989_);
        crate::leanh::lean_dec_ref(v_inst_1790_);
        v_toPure_1990_ = crate::leanh::lean_ctor_get(v_toApplicative_1987_, 1);
        crate::leanh::lean_inc_n(v_toPure_1990_, 2);
        crate::leanh::lean_dec_ref(v_toApplicative_1987_);
        v___x_1991_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1992_ = l_Lean_Syntax_getArg(v_x_1792_, v___x_1991_);
        crate::leanh::lean_dec(v_x_1792_);
        v___f_1993_ = crate::leanh::lean_alloc_closure(
            l_Std_Do_SPred_Notation_unpack___redArg___lam__17___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_1993_, 0, v_toPure_1990_);
        crate::leanh::lean_closure_set(v___f_1993_, 1, v___x_1992_);
        crate::leanh::lean_inc_ref(v_inst_1791_);
        v___f_1994_ = crate::leanh::lean_alloc_closure(
            l_Std_Do_SPred_Notation_unpack___redArg___lam__1___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_1994_, 0, v_inst_1791_);
        crate::leanh::lean_closure_set(v___f_1994_, 1, v_toBind_1988_);
        crate::leanh::lean_closure_set(v___f_1994_, 2, v___f_1993_);
        v___f_1995_ = crate::leanh::lean_alloc_closure(
            l_Std_Do_SPred_Notation_unpack___redArg___lam__2___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_1995_, 0, v_inst_1791_);
        crate::leanh::lean_closure_set(v___f_1995_, 1, v_toBind_1988_);
        crate::leanh::lean_closure_set(v___f_1995_, 2, v___f_1994_);
        v___f_1996_ = crate::leanh::lean_alloc_closure(
            l_Std_Do_SPred_Notation_unpack___redArg___lam__22___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_1996_, 0, v_toPure_1990_);
        v___x_1997_ = crate::leanh::lean_apply_4(
            v_toBind_1988_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getRef_1989_,
            v___f_1996_,
        );
        v___x_1998_ = crate::leanh::lean_apply_4(
            v_toBind_1988_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1997_,
            v___f_1995_,
        );
        return v___x_1998_;
    }
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___redArg___lam__11(
    mut v_inst_1999_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_2000_: *mut crate::leanh::LeanObject,
    mut v_inst_2001_: *mut crate::leanh::LeanObject,
    mut v___x_2002_: *mut crate::leanh::LeanObject,
    mut v___x_2003_: *mut crate::leanh::LeanObject,
    mut v_toBind_2004_: *mut crate::leanh::LeanObject,
    mut v___x_2005_: u8,
    mut v_inst_2006_: *mut crate::leanh::LeanObject,
    mut v_e_2007_: *mut crate::leanh::LeanObject,
    mut v_t_2008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2009_ = crate::leanh::lean_box((v___x_2005_) as usize);
    crate::leanh::lean_inc(v_toBind_2004_);
    crate::leanh::lean_inc_ref(v_inst_2001_);
    crate::leanh::lean_inc_ref(v_inst_1999_);
    v___f_2010_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_SPred_Notation_unpack___redArg___lam__13___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_2010_, 0, v_inst_1999_);
    crate::leanh::lean_closure_set(v___f_2010_, 1, v_toApplicative_2000_);
    crate::leanh::lean_closure_set(v___f_2010_, 2, v_inst_2001_);
    crate::leanh::lean_closure_set(v___f_2010_, 3, v___x_2002_);
    crate::leanh::lean_closure_set(v___f_2010_, 4, v___x_2003_);
    crate::leanh::lean_closure_set(v___f_2010_, 5, v_t_2008_);
    crate::leanh::lean_closure_set(v___f_2010_, 6, v_toBind_2004_);
    crate::leanh::lean_closure_set(v___f_2010_, 7, v___x_2009_);
    v___x_2011_ = l_Std_Do_SPred_Notation_unpack___redArg(
        v_inst_2006_,
        v_inst_1999_,
        v_inst_2001_,
        v_e_2007_,
    );
    v___x_2012_ = crate::leanh::lean_apply_4(
        v_toBind_2004_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2011_,
        v___f_2010_,
    );
    return v___x_2012_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack(
    mut v_m_2013_: *mut crate::leanh::LeanObject,
    mut v_inst_2014_: *mut crate::leanh::LeanObject,
    mut v_inst_2015_: *mut crate::leanh::LeanObject,
    mut v_inst_2016_: *mut crate::leanh::LeanObject,
    mut v_x_2017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Do_SPred_SPred(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Do_SPred_Notation_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Do_SPred_Notation_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Do_SPred_SPred(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Do_SPred_Notation_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Do_SPred_Notation_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Do_SPred_Notation_Basic(builtin);
}
