// Lean compiler output
// Module: Std.Internal.Do.Triple.Basic
// Imports: Std.Internal.Do.WP
use crate::ffi::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node7, l_Lean_addMacroScope, l_Lean_replaceRef,
    l_String_toRawSubstring_x27,
};
use crate::r#gen::Std::Internal::Do::WP::{
    initialize_Std_Internal_Do_WP, runtime_initialize_Std_Internal_Do_WP,
};
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value:
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
    m_data: [83, 116, 100, 0],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value:
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
    m_data: [73, 110, 116, 101, 114, 110, 97, 108, 0],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value:
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
    m_data: [68, 111, 0],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__3_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 11,
    m_data: [
        116, 101, 114, 109, 226, 166, 131, 95, 226, 166, 132, 95, 226, 166, 131, 95, 226, 166, 132,
        0,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_1:
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
            l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value)
            as *mut crate::leanh::LeanObject,
        1742885236933170401 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_2:
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
            l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value)
            as *mut crate::leanh::LeanObject,
        1237304041707523237 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value:
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
            l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__3_value)
            as *mut crate::leanh::LeanObject,
        14221277149122107325 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__5_value:
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
    m_data: [97, 110, 100, 116, 104, 101, 110, 0],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__5_value)
            as *mut crate::leanh::LeanObject,
        12571085391447129896 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 2,
    m_data: [226, 166, 131, 32, 0],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__8_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__9_value:
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
    m_data: [116, 101, 114, 109, 0],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__10_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__9_value)
            as *mut crate::leanh::LeanObject,
        8609355255726335675 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__10_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__12_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 3,
    m_data: [32, 226, 166, 132, 32, 0],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__14_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__15_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__12_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__14_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__16_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__15_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 3,
    m_data: [32, 226, 166, 131, 32, 0],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__18_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__19_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__16_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__18_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__20_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__19_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 2,
    m_data: [32, 226, 166, 132, 0],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__22_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__22:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__23_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__20_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__22_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__23:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__24_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value)
            as *mut crate::leanh::LeanObject,
        (((60 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__23_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__24:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__3_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 114, 105, 112, 108, 101, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5_value) as *mut crate::leanh::LeanObject,12441331751180145720 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7_value) as *mut crate::leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value) as *mut crate::leanh::LeanObject,1742885236933170401 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value) as *mut crate::leanh::LeanObject,1237304041707523237 as *mut crate::leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5_value) as *mut crate::leanh::LeanObject,9297738788347984318 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__10_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__11_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__13_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__13_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 114, 100, 101, 114, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 5, m_data: [116, 101, 114, 109, 226, 138, 165, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16_value) as *mut crate::leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15_value) as *mut crate::leanh::LeanObject,489434913524309295 as *mut crate::leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16_value) as *mut crate::leanh::LeanObject,14079511657030373096 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 138, 165, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__0_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__0_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 13,
    m_data: [
        116, 101, 114, 109, 226, 166, 131, 95, 226, 166, 132, 95, 226, 166, 131, 95, 44, 95, 226,
        166, 132, 0,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_1:
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
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value)
            as *mut crate::leanh::LeanObject,
        1742885236933170401 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_2:
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
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value)
            as *mut crate::leanh::LeanObject,
        1237304041707523237 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value:
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
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        14703663799162239584 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__2_value:
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
    m_data: [44, 32, 0],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__4_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__20_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__3_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__5_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__6_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__5_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__22_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__7_value:
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
        core::ptr::addr_of!(
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        (((60 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__6_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__0_value) as *mut crate::leanh::LeanObject,7932075773091973500 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__2_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__2_value) as *mut crate::leanh::LeanObject,7306243862518720553 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__5_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__5_value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__7_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value) as *mut crate::leanh::LeanObject,1742885236933170401 as *mut crate::leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value) as *mut crate::leanh::LeanObject,1237304041707523237 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__10_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__10_value) as *mut crate::leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15_value) as *mut crate::leanh::LeanObject,489434913524309295 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__12_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__13_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__12_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__14_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__10_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__13_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__15_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [102, 117, 110, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__15_value) as *mut crate::leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__15_value) as *mut crate::leanh::LeanObject,7043493786777132025 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__17_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 97, 115, 105, 99, 70, 117, 110, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__17_value) as *mut crate::leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__17_value) as *mut crate::leanh::LeanObject,16077784126176397009 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__20_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__21_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__21_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_475_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5;
    v___x_476_ = l_String_toRawSubstring_x27(v___x_475_);
    return v___x_476_;
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1(
    mut v_x_505_: *mut crate::leanh::LeanObject,
    mut v_a_506_: *mut crate::leanh::LeanObject,
    mut v_a_507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: u8 = 0;
    v___x_508_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4;
    crate::leanh::lean_inc(v_x_505_);
    v___x_509_ = l_Lean_Syntax_isOfKind(v_x_505_, v___x_508_);
    if v___x_509_ == 0 {
        let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_505_);
        v___x_510_ = crate::leanh::lean_box(1);
        v___x_511_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_511_, 0, v___x_510_);
        crate::leanh::lean_ctor_set(v___x_511_, 1, v_a_507_);
        return v___x_511_;
    } else {
        let mut v_quotContext_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_521_: u8 = 0;
        let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_512_ = crate::leanh::lean_ctor_get(v_a_506_, 1);
        v_currMacroScope_513_ = crate::leanh::lean_ctor_get(v_a_506_, 2);
        v_ref_514_ = crate::leanh::lean_ctor_get(v_a_506_, 5);
        v___x_515_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_516_ = l_Lean_Syntax_getArg(v_x_505_, v___x_515_);
        v___x_517_ = crate::leanh::lean_unsigned_to_nat(3);
        v___x_518_ = l_Lean_Syntax_getArg(v_x_505_, v___x_517_);
        v___x_519_ = crate::leanh::lean_unsigned_to_nat(5);
        v___x_520_ = l_Lean_Syntax_getArg(v_x_505_, v___x_519_);
        crate::leanh::lean_dec(v_x_505_);
        v___x_521_ = 0;
        v___x_522_ = l_Lean_SourceInfo_fromRef(v_ref_514_, v___x_521_);
        v___x_523_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4;
        v___x_524_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6);
        v___x_525_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7;
        crate::leanh::lean_inc(v_currMacroScope_513_);
        crate::leanh::lean_inc(v_quotContext_512_);
        v___x_526_ = l_Lean_addMacroScope(v_quotContext_512_, v___x_525_, v_currMacroScope_513_);
        v___x_527_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12;
        crate::leanh::lean_inc_n(v___x_522_, 4);
        v___x_528_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_528_, 0, v___x_522_);
        crate::leanh::lean_ctor_set(v___x_528_, 1, v___x_524_);
        crate::leanh::lean_ctor_set(v___x_528_, 2, v___x_526_);
        crate::leanh::lean_ctor_set(v___x_528_, 3, v___x_527_);
        v___x_529_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14;
        v___x_530_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17;
        v___x_531_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18;
        v___x_532_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_532_, 0, v___x_522_);
        crate::leanh::lean_ctor_set(v___x_532_, 1, v___x_531_);
        v___x_533_ = l_Lean_Syntax_node1(v___x_522_, v___x_530_, v___x_532_);
        v___x_534_ = l_Lean_Syntax_node4(
            v___x_522_, v___x_529_, v___x_516_, v___x_518_, v___x_520_, v___x_533_,
        );
        v___x_535_ = l_Lean_Syntax_node2(v___x_522_, v___x_523_, v___x_528_, v___x_534_);
        v___x_536_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_536_, 0, v___x_535_);
        crate::leanh::lean_ctor_set(v___x_536_, 1, v_a_507_);
        return v___x_536_;
    }
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___boxed(
    mut v_x_537_: *mut crate::leanh::LeanObject,
    mut v_a_538_: *mut crate::leanh::LeanObject,
    mut v_a_539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_540_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1(v_x_537_, v_a_538_, v_a_539_);
    crate::leanh::lean_dec_ref(v_a_538_);
    return v_res_540_;
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1(
    mut v_x_544_: *mut crate::leanh::LeanObject,
    mut v_a_545_: *mut crate::leanh::LeanObject,
    mut v_a_546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: u8 = 0;
    v___x_547_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4;
    crate::leanh::lean_inc(v_x_544_);
    v___x_548_ = l_Lean_Syntax_isOfKind(v_x_544_, v___x_547_);
    if v___x_548_ == 0 {
        let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_544_);
        v___x_549_ = crate::leanh::lean_box(0);
        v___x_550_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_550_, 0, v___x_549_);
        crate::leanh::lean_ctor_set(v___x_550_, 1, v_a_546_);
        return v___x_550_;
    } else {
        let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_554_: u8 = 0;
        v___x_551_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_552_ = l_Lean_Syntax_getArg(v_x_544_, v___x_551_);
        v___x_553_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__1;
        crate::leanh::lean_inc(v___x_552_);
        v___x_554_ = l_Lean_Syntax_isOfKind(v___x_552_, v___x_553_);
        if v___x_554_ == 0 {
            let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_552_);
            crate::leanh::lean_dec(v_x_544_);
            v___x_555_ = crate::leanh::lean_box(0);
            v___x_556_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_556_, 0, v___x_555_);
            crate::leanh::lean_ctor_set(v___x_556_, 1, v_a_546_);
            return v___x_556_;
        } else {
            let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_560_: u8 = 0;
            v___x_557_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_558_ = l_Lean_Syntax_getArg(v_x_544_, v___x_557_);
            crate::leanh::lean_dec(v_x_544_);
            v___x_559_ = crate::leanh::lean_unsigned_to_nat(4);
            crate::leanh::lean_inc(v___x_558_);
            v___x_560_ = l_Lean_Syntax_matchesNull(v___x_558_, v___x_559_);
            if v___x_560_ == 0 {
                let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_558_);
                crate::leanh::lean_dec(v___x_552_);
                v___x_561_ = crate::leanh::lean_box(0);
                v___x_562_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_562_, 0, v___x_561_);
                crate::leanh::lean_ctor_set(v___x_562_, 1, v_a_546_);
                return v___x_562_;
            } else {
                let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_566_: u8 = 0;
                v___x_563_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_564_ = l_Lean_Syntax_getArg(v___x_558_, v___x_563_);
                v___x_565_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17;
                v___x_566_ = l_Lean_Syntax_isOfKind(v___x_564_, v___x_565_);
                if v___x_566_ == 0 {
                    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_558_);
                    crate::leanh::lean_dec(v___x_552_);
                    v___x_567_ = crate::leanh::lean_box(0);
                    v___x_568_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_568_, 0, v___x_567_);
                    crate::leanh::lean_ctor_set(v___x_568_, 1, v_a_546_);
                    return v___x_568_;
                } else {
                    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_ref_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_574_: u8 = 0;
                    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_569_ = l_Lean_Syntax_getArg(v___x_558_, v___x_551_);
                    v___x_570_ = l_Lean_Syntax_getArg(v___x_558_, v___x_557_);
                    v___x_571_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_572_ = l_Lean_Syntax_getArg(v___x_558_, v___x_571_);
                    crate::leanh::lean_dec(v___x_558_);
                    v_ref_573_ = l_Lean_replaceRef(v___x_552_, v_a_545_);
                    crate::leanh::lean_dec(v___x_552_);
                    v___x_574_ = 0;
                    v___x_575_ = l_Lean_SourceInfo_fromRef(v_ref_573_, v___x_574_);
                    crate::leanh::lean_dec(v_ref_573_);
                    v___x_576_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4;
                    v___x_577_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7;
                    crate::leanh::lean_inc_n(v___x_575_, 4);
                    v___x_578_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_578_, 0, v___x_575_);
                    crate::leanh::lean_ctor_set(v___x_578_, 1, v___x_577_);
                    v___x_579_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13;
                    v___x_580_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_580_, 0, v___x_575_);
                    crate::leanh::lean_ctor_set(v___x_580_, 1, v___x_579_);
                    v___x_581_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17;
                    v___x_582_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_582_, 0, v___x_575_);
                    crate::leanh::lean_ctor_set(v___x_582_, 1, v___x_581_);
                    v___x_583_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21;
                    v___x_584_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_584_, 0, v___x_575_);
                    crate::leanh::lean_ctor_set(v___x_584_, 1, v___x_583_);
                    v___x_585_ = l_Lean_Syntax_node7(
                        v___x_575_, v___x_576_, v___x_578_, v___x_569_, v___x_580_, v___x_570_,
                        v___x_582_, v___x_572_, v___x_584_,
                    );
                    v___x_586_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_586_, 0, v___x_585_);
                    crate::leanh::lean_ctor_set(v___x_586_, 1, v_a_546_);
                    return v___x_586_;
                }
            }
        }
    }
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___boxed(
    mut v_x_587_: *mut crate::leanh::LeanObject,
    mut v_a_588_: *mut crate::leanh::LeanObject,
    mut v_a_589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_590_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1(v_x_587_, v_a_588_, v_a_589_);
    crate::leanh::lean_dec(v_a_588_);
    return v_res_590_;
}
pub unsafe fn _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_634_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__7;
    v___x_635_ = l_String_toRawSubstring_x27(v___x_634_);
    return v___x_635_;
}
pub unsafe fn _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_665_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_665_;
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1(
    mut v_x_668_: *mut crate::leanh::LeanObject,
    mut v_a_669_: *mut crate::leanh::LeanObject,
    mut v_a_670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: u8 = 0;
    v___x_671_ = l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1;
    crate::leanh::lean_inc(v_x_668_);
    v___x_672_ = l_Lean_Syntax_isOfKind(v_x_668_, v___x_671_);
    if v___x_672_ == 0 {
        let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_668_);
        v___x_673_ = crate::leanh::lean_box(1);
        v___x_674_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_674_, 0, v___x_673_);
        crate::leanh::lean_ctor_set(v___x_674_, 1, v_a_670_);
        return v___x_674_;
    } else {
        let mut v_quotContext_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_686_: u8 = 0;
        let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_675_ = crate::leanh::lean_ctor_get(v_a_669_, 1);
        v_currMacroScope_676_ = crate::leanh::lean_ctor_get(v_a_669_, 2);
        v_ref_677_ = crate::leanh::lean_ctor_get(v_a_669_, 5);
        v___x_678_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_679_ = l_Lean_Syntax_getArg(v_x_668_, v___x_678_);
        v___x_680_ = crate::leanh::lean_unsigned_to_nat(3);
        v___x_681_ = l_Lean_Syntax_getArg(v_x_668_, v___x_680_);
        v___x_682_ = crate::leanh::lean_unsigned_to_nat(5);
        v___x_683_ = l_Lean_Syntax_getArg(v_x_668_, v___x_682_);
        v___x_684_ = crate::leanh::lean_unsigned_to_nat(7);
        v___x_685_ = l_Lean_Syntax_getArg(v_x_668_, v___x_684_);
        crate::leanh::lean_dec(v_x_668_);
        v___x_686_ = 0;
        v___x_687_ = l_Lean_SourceInfo_fromRef(v_ref_677_, v___x_686_);
        v___x_688_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4;
        v___x_689_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6);
        v___x_690_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7;
        crate::leanh::lean_inc_n(v_currMacroScope_676_, 2);
        crate::leanh::lean_inc_n(v_quotContext_675_, 2);
        v___x_691_ = l_Lean_addMacroScope(v_quotContext_675_, v___x_690_, v_currMacroScope_676_);
        v___x_692_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12;
        crate::leanh::lean_inc_n(v___x_687_, 16);
        v___x_693_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_693_, 0, v___x_687_);
        crate::leanh::lean_ctor_set(v___x_693_, 1, v___x_689_);
        crate::leanh::lean_ctor_set(v___x_693_, 2, v___x_691_);
        crate::leanh::lean_ctor_set(v___x_693_, 3, v___x_692_);
        v___x_694_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14;
        v___x_695_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1;
        v___x_696_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3;
        v___x_697_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__4;
        v___x_698_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_698_, 0, v___x_687_);
        crate::leanh::lean_ctor_set(v___x_698_, 1, v___x_697_);
        v___x_699_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__6;
        v___x_700_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8);
        v___x_701_ = crate::leanh::lean_box(0);
        v___x_702_ = l_Lean_addMacroScope(v_quotContext_675_, v___x_701_, v_currMacroScope_676_);
        v___x_703_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__14;
        v___x_704_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_704_, 0, v___x_687_);
        crate::leanh::lean_ctor_set(v___x_704_, 1, v___x_700_);
        crate::leanh::lean_ctor_set(v___x_704_, 2, v___x_702_);
        crate::leanh::lean_ctor_set(v___x_704_, 3, v___x_703_);
        v___x_705_ = l_Lean_Syntax_node1(v___x_687_, v___x_699_, v___x_704_);
        v___x_706_ = l_Lean_Syntax_node2(v___x_687_, v___x_696_, v___x_698_, v___x_705_);
        v___x_707_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__15;
        v___x_708_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16;
        v___x_709_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_709_, 0, v___x_687_);
        crate::leanh::lean_ctor_set(v___x_709_, 1, v___x_707_);
        v___x_710_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18;
        v___x_711_ = l_Lean_Syntax_node1(v___x_687_, v___x_694_, v___x_683_);
        v___x_712_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19);
        v___x_713_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_713_, 0, v___x_687_);
        crate::leanh::lean_ctor_set(v___x_713_, 1, v___x_694_);
        crate::leanh::lean_ctor_set(v___x_713_, 2, v___x_712_);
        v___x_714_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__20;
        v___x_715_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_715_, 0, v___x_687_);
        crate::leanh::lean_ctor_set(v___x_715_, 1, v___x_714_);
        v___x_716_ = l_Lean_Syntax_node4(
            v___x_687_, v___x_710_, v___x_711_, v___x_713_, v___x_715_, v___x_685_,
        );
        v___x_717_ = l_Lean_Syntax_node2(v___x_687_, v___x_708_, v___x_709_, v___x_716_);
        v___x_718_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__21;
        v___x_719_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_719_, 0, v___x_687_);
        crate::leanh::lean_ctor_set(v___x_719_, 1, v___x_718_);
        v___x_720_ =
            l_Lean_Syntax_node3(v___x_687_, v___x_695_, v___x_706_, v___x_717_, v___x_719_);
        v___x_721_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17;
        v___x_722_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18;
        v___x_723_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_723_, 0, v___x_687_);
        crate::leanh::lean_ctor_set(v___x_723_, 1, v___x_722_);
        v___x_724_ = l_Lean_Syntax_node1(v___x_687_, v___x_721_, v___x_723_);
        v___x_725_ = l_Lean_Syntax_node4(
            v___x_687_, v___x_694_, v___x_679_, v___x_681_, v___x_720_, v___x_724_,
        );
        v___x_726_ = l_Lean_Syntax_node2(v___x_687_, v___x_688_, v___x_693_, v___x_725_);
        v___x_727_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_727_, 0, v___x_726_);
        crate::leanh::lean_ctor_set(v___x_727_, 1, v_a_670_);
        return v___x_727_;
    }
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___boxed(
    mut v_x_728_: *mut crate::leanh::LeanObject,
    mut v_a_729_: *mut crate::leanh::LeanObject,
    mut v_a_730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_731_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1(v_x_728_, v_a_729_, v_a_730_);
    crate::leanh::lean_dec_ref(v_a_729_);
    return v_res_731_;
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__2(
    mut v_x_732_: *mut crate::leanh::LeanObject,
    mut v_a_733_: *mut crate::leanh::LeanObject,
    mut v_a_734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: u8 = 0;
    v___x_735_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4;
    crate::leanh::lean_inc(v_x_732_);
    v___x_736_ = l_Lean_Syntax_isOfKind(v_x_732_, v___x_735_);
    if v___x_736_ == 0 {
        let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_732_);
        v___x_737_ = crate::leanh::lean_box(0);
        v___x_738_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_738_, 0, v___x_737_);
        crate::leanh::lean_ctor_set(v___x_738_, 1, v_a_734_);
        return v___x_738_;
    } else {
        let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_742_: u8 = 0;
        v___x_739_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_740_ = l_Lean_Syntax_getArg(v_x_732_, v___x_739_);
        v___x_741_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__1;
        crate::leanh::lean_inc(v___x_740_);
        v___x_742_ = l_Lean_Syntax_isOfKind(v___x_740_, v___x_741_);
        if v___x_742_ == 0 {
            let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_740_);
            crate::leanh::lean_dec(v_x_732_);
            v___x_743_ = crate::leanh::lean_box(0);
            v___x_744_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_744_, 0, v___x_743_);
            crate::leanh::lean_ctor_set(v___x_744_, 1, v_a_734_);
            return v___x_744_;
        } else {
            let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_748_: u8 = 0;
            v___x_745_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_746_ = l_Lean_Syntax_getArg(v_x_732_, v___x_745_);
            crate::leanh::lean_dec(v_x_732_);
            v___x_747_ = crate::leanh::lean_unsigned_to_nat(4);
            crate::leanh::lean_inc(v___x_746_);
            v___x_748_ = l_Lean_Syntax_matchesNull(v___x_746_, v___x_747_);
            if v___x_748_ == 0 {
                let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_746_);
                crate::leanh::lean_dec(v___x_740_);
                v___x_749_ = crate::leanh::lean_box(0);
                v___x_750_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_750_, 0, v___x_749_);
                crate::leanh::lean_ctor_set(v___x_750_, 1, v_a_734_);
                return v___x_750_;
            } else {
                let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_754_: u8 = 0;
                v___x_751_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_752_ = l_Lean_Syntax_getArg(v___x_746_, v___x_751_);
                v___x_753_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16;
                crate::leanh::lean_inc(v___x_752_);
                v___x_754_ = l_Lean_Syntax_isOfKind(v___x_752_, v___x_753_);
                if v___x_754_ == 0 {
                    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_752_);
                    crate::leanh::lean_dec(v___x_746_);
                    crate::leanh::lean_dec(v___x_740_);
                    v___x_755_ = crate::leanh::lean_box(0);
                    v___x_756_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_756_, 0, v___x_755_);
                    crate::leanh::lean_ctor_set(v___x_756_, 1, v_a_734_);
                    return v___x_756_;
                } else {
                    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_759_: u8 = 0;
                    v___x_757_ = l_Lean_Syntax_getArg(v___x_752_, v___x_745_);
                    crate::leanh::lean_dec(v___x_752_);
                    v___x_758_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18;
                    crate::leanh::lean_inc(v___x_757_);
                    v___x_759_ = l_Lean_Syntax_isOfKind(v___x_757_, v___x_758_);
                    if v___x_759_ == 0 {
                        let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v___x_757_);
                        crate::leanh::lean_dec(v___x_746_);
                        crate::leanh::lean_dec(v___x_740_);
                        v___x_760_ = crate::leanh::lean_box(0);
                        v___x_761_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_761_, 0, v___x_760_);
                        crate::leanh::lean_ctor_set(v___x_761_, 1, v_a_734_);
                        return v___x_761_;
                    } else {
                        let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_763_: u8 = 0;
                        v___x_762_ = l_Lean_Syntax_getArg(v___x_757_, v___x_739_);
                        crate::leanh::lean_inc(v___x_762_);
                        v___x_763_ = l_Lean_Syntax_matchesNull(v___x_762_, v___x_745_);
                        if v___x_763_ == 0 {
                            let mut v___x_764_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_765_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v___x_762_);
                            crate::leanh::lean_dec(v___x_757_);
                            crate::leanh::lean_dec(v___x_746_);
                            crate::leanh::lean_dec(v___x_740_);
                            v___x_764_ = crate::leanh::lean_box(0);
                            v___x_765_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_765_, 0, v___x_764_);
                            crate::leanh::lean_ctor_set(v___x_765_, 1, v_a_734_);
                            return v___x_765_;
                        } else {
                            let mut v___x_766_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_767_: u8 = 0;
                            v___x_766_ = l_Lean_Syntax_getArg(v___x_757_, v___x_745_);
                            v___x_767_ = l_Lean_Syntax_matchesNull(v___x_766_, v___x_739_);
                            if v___x_767_ == 0 {
                                let mut v___x_768_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_769_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                crate::leanh::lean_dec(v___x_762_);
                                crate::leanh::lean_dec(v___x_757_);
                                crate::leanh::lean_dec(v___x_746_);
                                crate::leanh::lean_dec(v___x_740_);
                                v___x_768_ = crate::leanh::lean_box(0);
                                v___x_769_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_769_, 0, v___x_768_);
                                crate::leanh::lean_ctor_set(v___x_769_, 1, v_a_734_);
                                return v___x_769_;
                            } else {
                                let mut v___x_770_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_771_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_772_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_773_: u8 = 0;
                                v___x_770_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_771_ = l_Lean_Syntax_getArg(v___x_746_, v___x_770_);
                                v___x_772_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17;
                                v___x_773_ = l_Lean_Syntax_isOfKind(v___x_771_, v___x_772_);
                                if v___x_773_ == 0 {
                                    let mut v___x_774_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_775_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    crate::leanh::lean_dec(v___x_762_);
                                    crate::leanh::lean_dec(v___x_757_);
                                    crate::leanh::lean_dec(v___x_746_);
                                    crate::leanh::lean_dec(v___x_740_);
                                    v___x_774_ = crate::leanh::lean_box(0);
                                    v___x_775_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_775_, 0, v___x_774_);
                                    crate::leanh::lean_ctor_set(v___x_775_, 1, v_a_734_);
                                    return v___x_775_;
                                } else {
                                    let mut v___x_776_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_777_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_778_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_779_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v_ref_780_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_781_: u8 = 0;
                                    let mut v___x_782_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_783_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_784_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_785_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_786_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_787_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_788_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_789_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_790_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_791_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_792_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_793_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_794_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_795_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_796_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_797_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_798_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_799_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_800_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_801_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_802_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_803_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_804_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_805_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_806_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    v___x_776_ = l_Lean_Syntax_getArg(v___x_746_, v___x_739_);
                                    v___x_777_ = l_Lean_Syntax_getArg(v___x_746_, v___x_745_);
                                    crate::leanh::lean_dec(v___x_746_);
                                    v___x_778_ = l_Lean_Syntax_getArg(v___x_762_, v___x_739_);
                                    crate::leanh::lean_dec(v___x_762_);
                                    v___x_779_ = l_Lean_Syntax_getArg(v___x_757_, v___x_770_);
                                    crate::leanh::lean_dec(v___x_757_);
                                    v_ref_780_ = l_Lean_replaceRef(v___x_740_, v_a_733_);
                                    crate::leanh::lean_dec(v___x_740_);
                                    v___x_781_ = 0;
                                    v___x_782_ = l_Lean_SourceInfo_fromRef(v_ref_780_, v___x_781_);
                                    crate::leanh::lean_dec(v_ref_780_);
                                    v___x_783_ = l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1;
                                    v___x_784_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7;
                                    crate::leanh::lean_inc_n(v___x_782_, 5);
                                    v___x_785_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_785_, 0, v___x_782_);
                                    crate::leanh::lean_ctor_set(v___x_785_, 1, v___x_784_);
                                    v___x_786_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13;
                                    v___x_787_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_787_, 0, v___x_782_);
                                    crate::leanh::lean_ctor_set(v___x_787_, 1, v___x_786_);
                                    v___x_788_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17;
                                    v___x_789_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_789_, 0, v___x_782_);
                                    crate::leanh::lean_ctor_set(v___x_789_, 1, v___x_788_);
                                    v___x_790_ = l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__2;
                                    v___x_791_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_791_, 0, v___x_782_);
                                    crate::leanh::lean_ctor_set(v___x_791_, 1, v___x_790_);
                                    v___x_792_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21;
                                    v___x_793_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_793_, 0, v___x_782_);
                                    crate::leanh::lean_ctor_set(v___x_793_, 1, v___x_792_);
                                    v___x_794_ = crate::leanh::lean_unsigned_to_nat(9);
                                    v___x_795_ = lean_mk_empty_array_with_capacity(v___x_794_);
                                    v___x_796_ = lean_array_push(v___x_795_, v___x_785_);
                                    v___x_797_ = lean_array_push(v___x_796_, v___x_776_);
                                    v___x_798_ = lean_array_push(v___x_797_, v___x_787_);
                                    v___x_799_ = lean_array_push(v___x_798_, v___x_777_);
                                    v___x_800_ = lean_array_push(v___x_799_, v___x_789_);
                                    v___x_801_ = lean_array_push(v___x_800_, v___x_778_);
                                    v___x_802_ = lean_array_push(v___x_801_, v___x_791_);
                                    v___x_803_ = lean_array_push(v___x_802_, v___x_779_);
                                    v___x_804_ = lean_array_push(v___x_803_, v___x_793_);
                                    v___x_805_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_805_, 0, v___x_782_);
                                    crate::leanh::lean_ctor_set(v___x_805_, 1, v___x_783_);
                                    crate::leanh::lean_ctor_set(v___x_805_, 2, v___x_804_);
                                    v___x_806_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_806_, 0, v___x_805_);
                                    crate::leanh::lean_ctor_set(v___x_806_, 1, v_a_734_);
                                    return v___x_806_;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__2___boxed(
    mut v_x_807_: *mut crate::leanh::LeanObject,
    mut v_a_808_: *mut crate::leanh::LeanObject,
    mut v_a_809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_810_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__2(v_x_807_, v_a_808_, v_a_809_);
    crate::leanh::lean_dec(v_a_808_);
    return v_res_810_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_Do_Triple_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Internal_Do_WP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_Do_Triple_Basic(
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
pub unsafe fn initialize_Std_Internal_Do_Triple_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Internal_Do_WP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Do_Triple_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Internal_Do_Triple_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Internal_Do_Triple_Basic(builtin);
}
