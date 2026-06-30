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
    m_data: [83, 116, 100, 0],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value:
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
    m_data: [73, 110, 116, 101, 114, 110, 97, 108, 0],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value:
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
    m_data: [68, 111, 0],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__3_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__3_value)
        as *mut leanh::LeanObject;
static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_1:
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
            l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value)
            as *mut leanh::LeanObject,
        1742885236933170401 as *mut leanh::LeanObject,
    ],
};
static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_2:
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
            l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value)
            as *mut leanh::LeanObject,
        1237304041707523237 as *mut leanh::LeanObject,
    ],
};
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value:
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
            l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__3_value)
            as *mut leanh::LeanObject,
        14221277149122107325 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__5_value:
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
    m_data: [97, 110, 100, 116, 104, 101, 110, 0],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__5_value)
            as *mut leanh::LeanObject,
        12571085391447129896 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__8_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__9_value:
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
    m_data: [116, 101, 114, 109, 0],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__10_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__9_value)
            as *mut leanh::LeanObject,
        8609355255726335675 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__10_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__12_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__14_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__15_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__12_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__14_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__16_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__15_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__18_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__18:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__19_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__16_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__18_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__19:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__20_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__19_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__20:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__22_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__22:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__23_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__20_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__22_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__23:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__24_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4_value)
            as *mut leanh::LeanObject,
        (((60 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__23_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__24:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__24_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Internal_Do_term_u2983___u2984___u2983___u2984: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__3_value) as *mut leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__3_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 114, 105, 112, 108, 101, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5_value) as *mut leanh::LeanObject;
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5_value) as *mut leanh::LeanObject,12441331751180145720 as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7_value) as *mut leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value) as *mut leanh::LeanObject,1742885236933170401 as *mut leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value) as *mut leanh::LeanObject,1237304041707523237 as *mut leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5_value) as *mut leanh::LeanObject,9297738788347984318 as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__9_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__10_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__8_value) as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__11_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__10_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__9_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__11_value) as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__13_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__13_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 114, 100, 101, 114, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 5, m_data: [116, 101, 114, 109, 226, 138, 165, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16_value) as *mut leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15_value) as *mut leanh::LeanObject,489434913524309295 as *mut leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__16_value) as *mut leanh::LeanObject,14079511657030373096 as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 138, 165, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__0_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__0_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__0_value
) as *mut leanh::LeanObject;
static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_1:
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
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value)
            as *mut leanh::LeanObject,
        1742885236933170401 as *mut leanh::LeanObject,
    ],
};
static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_2:
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
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value)
            as *mut leanh::LeanObject,
        1237304041707523237 as *mut leanh::LeanObject,
    ],
};
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value:
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
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__0_value
        ) as *mut leanh::LeanObject,
        14703663799162239584 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__2_value:
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
    m_data: [44, 32, 0],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__2_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__4_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__20_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__3_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__5_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__4_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__11_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__6_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__5_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__22_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__7_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1_value
        ) as *mut leanh::LeanObject,
        (((60 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__6_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__7_value
) as *mut leanh::LeanObject;
pub static mut l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__0_value) as *mut leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__0_value) as *mut leanh::LeanObject,7932075773091973500 as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__2_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__2_value) as *mut leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__2_value) as *mut leanh::LeanObject,7306243862518720553 as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__4_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__5_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__5_value) as *mut leanh::LeanObject,9871775667037945883 as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__7_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__7_value) as *mut leanh::LeanObject;
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__1_value) as *mut leanh::LeanObject,1742885236933170401 as *mut leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__2_value) as *mut leanh::LeanObject,1237304041707523237 as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__10_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__9_value) as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__10_value) as *mut leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__15_value) as *mut leanh::LeanObject,489434913524309295 as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__12_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__11_value) as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__13_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__12_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__14_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__10_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__13_value) as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__15_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [102, 117, 110, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__15_value) as *mut leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__15_value) as *mut leanh::LeanObject,7043493786777132025 as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__17_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 97, 115, 105, 99, 70, 117, 110, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__17_value) as *mut leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__17_value) as *mut leanh::LeanObject,16077784126176397009 as *mut leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18_value) as *mut leanh::LeanObject;
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__20_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__20_value) as *mut leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__21_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__21_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_475_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__5;
    v___x_476_ = l_String_toRawSubstring_x27(v___x_475_);
    return v___x_476_;
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1(
    mut v_x_505_: *mut leanh::LeanObject,
    mut v_a_506_: *mut leanh::LeanObject,
    mut v_a_507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: u8 = 0;
    v___x_508_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4;
    leanh::lean_inc(v_x_505_);
    v___x_509_ = l_Lean_Syntax_isOfKind(v_x_505_, v___x_508_);
    if v___x_509_ == 0 {
        let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_505_);
        v___x_510_ = leanh::lean_box(1);
        v___x_511_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_511_, 0, v___x_510_);
        leanh::lean_ctor_set(v___x_511_, 1, v_a_507_);
        return v___x_511_;
    } else {
        let mut v_quotContext_512_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_513_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_514_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_516_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_520_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_521_: u8 = 0;
        let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_531_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_535_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_512_ = leanh::lean_ctor_get(v_a_506_, 1);
        v_currMacroScope_513_ = leanh::lean_ctor_get(v_a_506_, 2);
        v_ref_514_ = leanh::lean_ctor_get(v_a_506_, 5);
        v___x_515_ = leanh::lean_unsigned_to_nat(1);
        v___x_516_ = l_Lean_Syntax_getArg(v_x_505_, v___x_515_);
        v___x_517_ = leanh::lean_unsigned_to_nat(3);
        v___x_518_ = l_Lean_Syntax_getArg(v_x_505_, v___x_517_);
        v___x_519_ = leanh::lean_unsigned_to_nat(5);
        v___x_520_ = l_Lean_Syntax_getArg(v_x_505_, v___x_519_);
        leanh::lean_dec(v_x_505_);
        v___x_521_ = 0;
        v___x_522_ = l_Lean_SourceInfo_fromRef(v_ref_514_, v___x_521_);
        v___x_523_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4;
        v___x_524_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6);
        v___x_525_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7;
        leanh::lean_inc(v_currMacroScope_513_);
        leanh::lean_inc(v_quotContext_512_);
        v___x_526_ = l_Lean_addMacroScope(v_quotContext_512_, v___x_525_, v_currMacroScope_513_);
        v___x_527_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12;
        leanh::lean_inc_n(v___x_522_, 4);
        v___x_528_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_528_, 0, v___x_522_);
        leanh::lean_ctor_set(v___x_528_, 1, v___x_524_);
        leanh::lean_ctor_set(v___x_528_, 2, v___x_526_);
        leanh::lean_ctor_set(v___x_528_, 3, v___x_527_);
        v___x_529_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14;
        v___x_530_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17;
        v___x_531_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18;
        v___x_532_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_532_, 0, v___x_522_);
        leanh::lean_ctor_set(v___x_532_, 1, v___x_531_);
        v___x_533_ = l_Lean_Syntax_node1(v___x_522_, v___x_530_, v___x_532_);
        v___x_534_ = l_Lean_Syntax_node4(
            v___x_522_, v___x_529_, v___x_516_, v___x_518_, v___x_520_, v___x_533_,
        );
        v___x_535_ = l_Lean_Syntax_node2(v___x_522_, v___x_523_, v___x_528_, v___x_534_);
        v___x_536_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_536_, 0, v___x_535_);
        leanh::lean_ctor_set(v___x_536_, 1, v_a_507_);
        return v___x_536_;
    }
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___boxed(
    mut v_x_537_: *mut leanh::LeanObject,
    mut v_a_538_: *mut leanh::LeanObject,
    mut v_a_539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_540_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1(v_x_537_, v_a_538_, v_a_539_);
    leanh::lean_dec_ref(v_a_538_);
    return v_res_540_;
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1(
    mut v_x_544_: *mut leanh::LeanObject,
    mut v_a_545_: *mut leanh::LeanObject,
    mut v_a_546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: u8 = 0;
    v___x_547_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4;
    leanh::lean_inc(v_x_544_);
    v___x_548_ = l_Lean_Syntax_isOfKind(v_x_544_, v___x_547_);
    if v___x_548_ == 0 {
        let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_544_);
        v___x_549_ = leanh::lean_box(0);
        v___x_550_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_550_, 0, v___x_549_);
        leanh::lean_ctor_set(v___x_550_, 1, v_a_546_);
        return v___x_550_;
    } else {
        let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_554_: u8 = 0;
        v___x_551_ = leanh::lean_unsigned_to_nat(0);
        v___x_552_ = l_Lean_Syntax_getArg(v_x_544_, v___x_551_);
        v___x_553_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__1;
        leanh::lean_inc(v___x_552_);
        v___x_554_ = l_Lean_Syntax_isOfKind(v___x_552_, v___x_553_);
        if v___x_554_ == 0 {
            let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_552_);
            leanh::lean_dec(v_x_544_);
            v___x_555_ = leanh::lean_box(0);
            v___x_556_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_556_, 0, v___x_555_);
            leanh::lean_ctor_set(v___x_556_, 1, v_a_546_);
            return v___x_556_;
        } else {
            let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_560_: u8 = 0;
            v___x_557_ = leanh::lean_unsigned_to_nat(1);
            v___x_558_ = l_Lean_Syntax_getArg(v_x_544_, v___x_557_);
            leanh::lean_dec(v_x_544_);
            v___x_559_ = leanh::lean_unsigned_to_nat(4);
            leanh::lean_inc(v___x_558_);
            v___x_560_ = l_Lean_Syntax_matchesNull(v___x_558_, v___x_559_);
            if v___x_560_ == 0 {
                let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_558_);
                leanh::lean_dec(v___x_552_);
                v___x_561_ = leanh::lean_box(0);
                v___x_562_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_562_, 0, v___x_561_);
                leanh::lean_ctor_set(v___x_562_, 1, v_a_546_);
                return v___x_562_;
            } else {
                let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_566_: u8 = 0;
                v___x_563_ = leanh::lean_unsigned_to_nat(3);
                v___x_564_ = l_Lean_Syntax_getArg(v___x_558_, v___x_563_);
                v___x_565_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17;
                v___x_566_ = l_Lean_Syntax_isOfKind(v___x_564_, v___x_565_);
                if v___x_566_ == 0 {
                    let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v___x_558_);
                    leanh::lean_dec(v___x_552_);
                    v___x_567_ = leanh::lean_box(0);
                    v___x_568_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_568_, 0, v___x_567_);
                    leanh::lean_ctor_set(v___x_568_, 1, v_a_546_);
                    return v___x_568_;
                } else {
                    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_ref_573_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_574_: u8 = 0;
                    let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_577_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_580_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_581_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_582_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_583_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_569_ = l_Lean_Syntax_getArg(v___x_558_, v___x_551_);
                    v___x_570_ = l_Lean_Syntax_getArg(v___x_558_, v___x_557_);
                    v___x_571_ = leanh::lean_unsigned_to_nat(2);
                    v___x_572_ = l_Lean_Syntax_getArg(v___x_558_, v___x_571_);
                    leanh::lean_dec(v___x_558_);
                    v_ref_573_ = l_Lean_replaceRef(v___x_552_, v_a_545_);
                    leanh::lean_dec(v___x_552_);
                    v___x_574_ = 0;
                    v___x_575_ = l_Lean_SourceInfo_fromRef(v_ref_573_, v___x_574_);
                    leanh::lean_dec(v_ref_573_);
                    v___x_576_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__4;
                    v___x_577_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7;
                    leanh::lean_inc_n(v___x_575_, 4);
                    v___x_578_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_578_, 0, v___x_575_);
                    leanh::lean_ctor_set(v___x_578_, 1, v___x_577_);
                    v___x_579_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13;
                    v___x_580_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_580_, 0, v___x_575_);
                    leanh::lean_ctor_set(v___x_580_, 1, v___x_579_);
                    v___x_581_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17;
                    v___x_582_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_582_, 0, v___x_575_);
                    leanh::lean_ctor_set(v___x_582_, 1, v___x_581_);
                    v___x_583_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21;
                    v___x_584_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_584_, 0, v___x_575_);
                    leanh::lean_ctor_set(v___x_584_, 1, v___x_583_);
                    v___x_585_ = l_Lean_Syntax_node7(
                        v___x_575_, v___x_576_, v___x_578_, v___x_569_, v___x_580_, v___x_570_,
                        v___x_582_, v___x_572_, v___x_584_,
                    );
                    v___x_586_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_586_, 0, v___x_585_);
                    leanh::lean_ctor_set(v___x_586_, 1, v_a_546_);
                    return v___x_586_;
                }
            }
        }
    }
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___boxed(
    mut v_x_587_: *mut leanh::LeanObject,
    mut v_a_588_: *mut leanh::LeanObject,
    mut v_a_589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_590_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1(v_x_587_, v_a_588_, v_a_589_);
    leanh::lean_dec(v_a_588_);
    return v_res_590_;
}
pub unsafe fn _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_634_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__7;
    v___x_635_ = l_String_toRawSubstring_x27(v___x_634_);
    return v___x_635_;
}
pub unsafe fn _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_665_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_665_;
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1(
    mut v_x_668_: *mut leanh::LeanObject,
    mut v_a_669_: *mut leanh::LeanObject,
    mut v_a_670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: u8 = 0;
    v___x_671_ = l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1;
    leanh::lean_inc(v_x_668_);
    v___x_672_ = l_Lean_Syntax_isOfKind(v_x_668_, v___x_671_);
    if v___x_672_ == 0 {
        let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_668_);
        v___x_673_ = leanh::lean_box(1);
        v___x_674_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_674_, 0, v___x_673_);
        leanh::lean_ctor_set(v___x_674_, 1, v_a_670_);
        return v___x_674_;
    } else {
        let mut v_quotContext_675_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_676_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_677_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_681_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_686_: u8 = 0;
        let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_701_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_706_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_707_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_708_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_709_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_712_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_714_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_715_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_716_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_717_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_718_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_720_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_724_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_725_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_726_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_727_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_675_ = leanh::lean_ctor_get(v_a_669_, 1);
        v_currMacroScope_676_ = leanh::lean_ctor_get(v_a_669_, 2);
        v_ref_677_ = leanh::lean_ctor_get(v_a_669_, 5);
        v___x_678_ = leanh::lean_unsigned_to_nat(1);
        v___x_679_ = l_Lean_Syntax_getArg(v_x_668_, v___x_678_);
        v___x_680_ = leanh::lean_unsigned_to_nat(3);
        v___x_681_ = l_Lean_Syntax_getArg(v_x_668_, v___x_680_);
        v___x_682_ = leanh::lean_unsigned_to_nat(5);
        v___x_683_ = l_Lean_Syntax_getArg(v_x_668_, v___x_682_);
        v___x_684_ = leanh::lean_unsigned_to_nat(7);
        v___x_685_ = l_Lean_Syntax_getArg(v_x_668_, v___x_684_);
        leanh::lean_dec(v_x_668_);
        v___x_686_ = 0;
        v___x_687_ = l_Lean_SourceInfo_fromRef(v_ref_677_, v___x_686_);
        v___x_688_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4;
        v___x_689_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__6);
        v___x_690_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__7;
        leanh::lean_inc_n(v_currMacroScope_676_, 2);
        leanh::lean_inc_n(v_quotContext_675_, 2);
        v___x_691_ = l_Lean_addMacroScope(v_quotContext_675_, v___x_690_, v_currMacroScope_676_);
        v___x_692_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__12;
        leanh::lean_inc_n(v___x_687_, 16);
        v___x_693_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_693_, 0, v___x_687_);
        leanh::lean_ctor_set(v___x_693_, 1, v___x_689_);
        leanh::lean_ctor_set(v___x_693_, 2, v___x_691_);
        leanh::lean_ctor_set(v___x_693_, 3, v___x_692_);
        v___x_694_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__14;
        v___x_695_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__1;
        v___x_696_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__3;
        v___x_697_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__4;
        v___x_698_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_698_, 0, v___x_687_);
        leanh::lean_ctor_set(v___x_698_, 1, v___x_697_);
        v___x_699_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__6;
        v___x_700_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__8);
        v___x_701_ = leanh::lean_box(0);
        v___x_702_ = l_Lean_addMacroScope(v_quotContext_675_, v___x_701_, v_currMacroScope_676_);
        v___x_703_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__14;
        v___x_704_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_704_, 0, v___x_687_);
        leanh::lean_ctor_set(v___x_704_, 1, v___x_700_);
        leanh::lean_ctor_set(v___x_704_, 2, v___x_702_);
        leanh::lean_ctor_set(v___x_704_, 3, v___x_703_);
        v___x_705_ = l_Lean_Syntax_node1(v___x_687_, v___x_699_, v___x_704_);
        v___x_706_ = l_Lean_Syntax_node2(v___x_687_, v___x_696_, v___x_698_, v___x_705_);
        v___x_707_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__15;
        v___x_708_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16;
        v___x_709_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_709_, 0, v___x_687_);
        leanh::lean_ctor_set(v___x_709_, 1, v___x_707_);
        v___x_710_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18;
        v___x_711_ = l_Lean_Syntax_node1(v___x_687_, v___x_694_, v___x_683_);
        v___x_712_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__19);
        v___x_713_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_713_, 0, v___x_687_);
        leanh::lean_ctor_set(v___x_713_, 1, v___x_694_);
        leanh::lean_ctor_set(v___x_713_, 2, v___x_712_);
        v___x_714_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__20;
        v___x_715_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_715_, 0, v___x_687_);
        leanh::lean_ctor_set(v___x_715_, 1, v___x_714_);
        v___x_716_ = l_Lean_Syntax_node4(
            v___x_687_, v___x_710_, v___x_711_, v___x_713_, v___x_715_, v___x_685_,
        );
        v___x_717_ = l_Lean_Syntax_node2(v___x_687_, v___x_708_, v___x_709_, v___x_716_);
        v___x_718_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__21;
        v___x_719_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_719_, 0, v___x_687_);
        leanh::lean_ctor_set(v___x_719_, 1, v___x_718_);
        v___x_720_ =
            l_Lean_Syntax_node3(v___x_687_, v___x_695_, v___x_706_, v___x_717_, v___x_719_);
        v___x_721_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17;
        v___x_722_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__18;
        v___x_723_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_723_, 0, v___x_687_);
        leanh::lean_ctor_set(v___x_723_, 1, v___x_722_);
        v___x_724_ = l_Lean_Syntax_node1(v___x_687_, v___x_721_, v___x_723_);
        v___x_725_ = l_Lean_Syntax_node4(
            v___x_687_, v___x_694_, v___x_679_, v___x_681_, v___x_720_, v___x_724_,
        );
        v___x_726_ = l_Lean_Syntax_node2(v___x_687_, v___x_688_, v___x_693_, v___x_725_);
        v___x_727_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_727_, 0, v___x_726_);
        leanh::lean_ctor_set(v___x_727_, 1, v_a_670_);
        return v___x_727_;
    }
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___boxed(
    mut v_x_728_: *mut leanh::LeanObject,
    mut v_a_729_: *mut leanh::LeanObject,
    mut v_a_730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_731_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1(v_x_728_, v_a_729_, v_a_730_);
    leanh::lean_dec_ref(v_a_729_);
    return v_res_731_;
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__2(
    mut v_x_732_: *mut leanh::LeanObject,
    mut v_a_733_: *mut leanh::LeanObject,
    mut v_a_734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: u8 = 0;
    v___x_735_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__4;
    leanh::lean_inc(v_x_732_);
    v___x_736_ = l_Lean_Syntax_isOfKind(v_x_732_, v___x_735_);
    if v___x_736_ == 0 {
        let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_732_);
        v___x_737_ = leanh::lean_box(0);
        v___x_738_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_738_, 0, v___x_737_);
        leanh::lean_ctor_set(v___x_738_, 1, v_a_734_);
        return v___x_738_;
    } else {
        let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_740_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_742_: u8 = 0;
        v___x_739_ = leanh::lean_unsigned_to_nat(0);
        v___x_740_ = l_Lean_Syntax_getArg(v_x_732_, v___x_739_);
        v___x_741_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__1___closed__1;
        leanh::lean_inc(v___x_740_);
        v___x_742_ = l_Lean_Syntax_isOfKind(v___x_740_, v___x_741_);
        if v___x_742_ == 0 {
            let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_740_);
            leanh::lean_dec(v_x_732_);
            v___x_743_ = leanh::lean_box(0);
            v___x_744_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_744_, 0, v___x_743_);
            leanh::lean_ctor_set(v___x_744_, 1, v_a_734_);
            return v___x_744_;
        } else {
            let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_748_: u8 = 0;
            v___x_745_ = leanh::lean_unsigned_to_nat(1);
            v___x_746_ = l_Lean_Syntax_getArg(v_x_732_, v___x_745_);
            leanh::lean_dec(v_x_732_);
            v___x_747_ = leanh::lean_unsigned_to_nat(4);
            leanh::lean_inc(v___x_746_);
            v___x_748_ = l_Lean_Syntax_matchesNull(v___x_746_, v___x_747_);
            if v___x_748_ == 0 {
                let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_750_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_746_);
                leanh::lean_dec(v___x_740_);
                v___x_749_ = leanh::lean_box(0);
                v___x_750_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_750_, 0, v___x_749_);
                leanh::lean_ctor_set(v___x_750_, 1, v_a_734_);
                return v___x_750_;
            } else {
                let mut v___x_751_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_753_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_754_: u8 = 0;
                v___x_751_ = leanh::lean_unsigned_to_nat(2);
                v___x_752_ = l_Lean_Syntax_getArg(v___x_746_, v___x_751_);
                v___x_753_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__16;
                leanh::lean_inc(v___x_752_);
                v___x_754_ = l_Lean_Syntax_isOfKind(v___x_752_, v___x_753_);
                if v___x_754_ == 0 {
                    let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v___x_752_);
                    leanh::lean_dec(v___x_746_);
                    leanh::lean_dec(v___x_740_);
                    v___x_755_ = leanh::lean_box(0);
                    v___x_756_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_756_, 0, v___x_755_);
                    leanh::lean_ctor_set(v___x_756_, 1, v_a_734_);
                    return v___x_756_;
                } else {
                    let mut v___x_757_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_759_: u8 = 0;
                    v___x_757_ = l_Lean_Syntax_getArg(v___x_752_, v___x_745_);
                    leanh::lean_dec(v___x_752_);
                    v___x_758_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___x2c___u2984__1___closed__18;
                    leanh::lean_inc(v___x_757_);
                    v___x_759_ = l_Lean_Syntax_isOfKind(v___x_757_, v___x_758_);
                    if v___x_759_ == 0 {
                        let mut v___x_760_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
                        leanh::lean_dec(v___x_757_);
                        leanh::lean_dec(v___x_746_);
                        leanh::lean_dec(v___x_740_);
                        v___x_760_ = leanh::lean_box(0);
                        v___x_761_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_761_, 0, v___x_760_);
                        leanh::lean_ctor_set(v___x_761_, 1, v_a_734_);
                        return v___x_761_;
                    } else {
                        let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_763_: u8 = 0;
                        v___x_762_ = l_Lean_Syntax_getArg(v___x_757_, v___x_739_);
                        leanh::lean_inc(v___x_762_);
                        v___x_763_ = l_Lean_Syntax_matchesNull(v___x_762_, v___x_745_);
                        if v___x_763_ == 0 {
                            let mut v___x_764_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_765_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            leanh::lean_dec(v___x_762_);
                            leanh::lean_dec(v___x_757_);
                            leanh::lean_dec(v___x_746_);
                            leanh::lean_dec(v___x_740_);
                            v___x_764_ = leanh::lean_box(0);
                            v___x_765_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_765_, 0, v___x_764_);
                            leanh::lean_ctor_set(v___x_765_, 1, v_a_734_);
                            return v___x_765_;
                        } else {
                            let mut v___x_766_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_767_: u8 = 0;
                            v___x_766_ = l_Lean_Syntax_getArg(v___x_757_, v___x_745_);
                            v___x_767_ = l_Lean_Syntax_matchesNull(v___x_766_, v___x_739_);
                            if v___x_767_ == 0 {
                                let mut v___x_768_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_769_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                leanh::lean_dec(v___x_762_);
                                leanh::lean_dec(v___x_757_);
                                leanh::lean_dec(v___x_746_);
                                leanh::lean_dec(v___x_740_);
                                v___x_768_ = leanh::lean_box(0);
                                v___x_769_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_769_, 0, v___x_768_);
                                leanh::lean_ctor_set(v___x_769_, 1, v_a_734_);
                                return v___x_769_;
                            } else {
                                let mut v___x_770_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_771_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_772_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_773_: u8 = 0;
                                v___x_770_ = leanh::lean_unsigned_to_nat(3);
                                v___x_771_ = l_Lean_Syntax_getArg(v___x_746_, v___x_770_);
                                v___x_772_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______macroRules__Std__Internal__Do__term_u2983___u2984___u2983___u2984__1___closed__17;
                                v___x_773_ = l_Lean_Syntax_isOfKind(v___x_771_, v___x_772_);
                                if v___x_773_ == 0 {
                                    let mut v___x_774_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_775_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    leanh::lean_dec(v___x_762_);
                                    leanh::lean_dec(v___x_757_);
                                    leanh::lean_dec(v___x_746_);
                                    leanh::lean_dec(v___x_740_);
                                    v___x_774_ = leanh::lean_box(0);
                                    v___x_775_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_775_, 0, v___x_774_);
                                    leanh::lean_ctor_set(v___x_775_, 1, v_a_734_);
                                    return v___x_775_;
                                } else {
                                    let mut v___x_776_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_777_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_778_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_779_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v_ref_780_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_781_: u8 = 0;
                                    let mut v___x_782_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_783_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_784_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_785_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_786_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_787_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_788_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_789_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_790_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_791_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_792_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_793_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_794_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_795_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_796_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_797_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_798_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_799_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_800_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_801_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_802_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_803_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_804_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_805_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_806_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    v___x_776_ = l_Lean_Syntax_getArg(v___x_746_, v___x_739_);
                                    v___x_777_ = l_Lean_Syntax_getArg(v___x_746_, v___x_745_);
                                    leanh::lean_dec(v___x_746_);
                                    v___x_778_ = l_Lean_Syntax_getArg(v___x_762_, v___x_739_);
                                    leanh::lean_dec(v___x_762_);
                                    v___x_779_ = l_Lean_Syntax_getArg(v___x_757_, v___x_770_);
                                    leanh::lean_dec(v___x_757_);
                                    v_ref_780_ = l_Lean_replaceRef(v___x_740_, v_a_733_);
                                    leanh::lean_dec(v___x_740_);
                                    v___x_781_ = 0;
                                    v___x_782_ = l_Lean_SourceInfo_fromRef(v_ref_780_, v___x_781_);
                                    leanh::lean_dec(v_ref_780_);
                                    v___x_783_ = l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__1;
                                    v___x_784_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__7;
                                    leanh::lean_inc_n(v___x_782_, 5);
                                    v___x_785_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_785_, 0, v___x_782_);
                                    leanh::lean_ctor_set(v___x_785_, 1, v___x_784_);
                                    v___x_786_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__13;
                                    v___x_787_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_787_, 0, v___x_782_);
                                    leanh::lean_ctor_set(v___x_787_, 1, v___x_786_);
                                    v___x_788_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__17;
                                    v___x_789_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_789_, 0, v___x_782_);
                                    leanh::lean_ctor_set(v___x_789_, 1, v___x_788_);
                                    v___x_790_ = l_Std_Internal_Do_term_u2983___u2984___u2983___x2c___u2984___closed__2;
                                    v___x_791_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_791_, 0, v___x_782_);
                                    leanh::lean_ctor_set(v___x_791_, 1, v___x_790_);
                                    v___x_792_ = l_Std_Internal_Do_term_u2983___u2984___u2983___u2984___closed__21;
                                    v___x_793_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_793_, 0, v___x_782_);
                                    leanh::lean_ctor_set(v___x_793_, 1, v___x_792_);
                                    v___x_794_ = leanh::lean_unsigned_to_nat(9);
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
                                    v___x_805_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                    leanh::lean_ctor_set(v___x_805_, 0, v___x_782_);
                                    leanh::lean_ctor_set(v___x_805_, 1, v___x_783_);
                                    leanh::lean_ctor_set(v___x_805_, 2, v___x_804_);
                                    v___x_806_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_806_, 0, v___x_805_);
                                    leanh::lean_ctor_set(v___x_806_, 1, v_a_734_);
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
    mut v_x_807_: *mut leanh::LeanObject,
    mut v_a_808_: *mut leanh::LeanObject,
    mut v_a_809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_810_ = l_Std_Internal_Do___aux__Std__Internal__Do__Triple__Basic______unexpand__Std__Internal__Do__Triple__2(v_x_807_, v_a_808_, v_a_809_);
    leanh::lean_dec(v_a_808_);
    return v_res_810_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_Do_Triple_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Internal_Do_WP(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_Do_Triple_Basic(
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
pub unsafe fn initialize_Std_Internal_Do_Triple_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Internal_Do_WP(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Do_Triple_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Internal_Do_Triple_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Internal_Do_Triple_Basic(builtin);
}