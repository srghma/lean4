// Lean compiler output
// Module: Std.Internal.Do.ExceptPost
// Imports: Std.Internal.Do.Assertion
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Prelude::{
    l_Array_extract___redArg, l_Array_mkArray0, l_Array_mkArray4___redArg,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_getNumArgs, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_addMacroScope,
    l_String_toRawSubstring_x27,
};
use crate::r#gen::Std::Internal::Do::Assertion::{
    initialize_Std_Internal_Do_Assertion, runtime_initialize_Std_Internal_Do_Assertion,
};
use crate::ffi::lean_nat_dec_le;
pub static mut l_Std_Internal_Do_instPartialOrderNil: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Internal_Do_instCompleteLatticeNil: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__0_value:
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
static mut l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__1_value:
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
static mut l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__2_value:
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
static mut l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__3_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 12,
    m_data: [
        116, 101, 114, 109, 69, 80, 111, 115, 116, 226, 159, 168, 95, 226, 159, 169, 0,
    ],
};
static mut l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__1_value)
            as *mut crate::leanh::LeanObject,
        1742885236933170401 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__2_value)
            as *mut crate::leanh::LeanObject,
        1237304041707523237 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__3_value)
            as *mut crate::leanh::LeanObject,
        5173123521522702746 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__5_value:
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
static mut l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__6_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__5_value)
            as *mut crate::leanh::LeanObject,
        12571085391447129896 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 6,
    m_data: [69, 80, 111, 115, 116, 226, 159, 168, 0],
};
static mut l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__8_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__9_value:
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
static mut l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__10_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__9_value)
            as *mut crate::leanh::LeanObject,
        8609355255726335675 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__11_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__10_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12_value:
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
static mut l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__13_value:
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
static mut l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__14_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__15_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 8) as u16,
        other: 3,
        tag: 10,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__11_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__14_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__16_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__15_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 159, 169, 0],
};
static mut l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__18_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__19_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__16_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__18_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__20_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__19_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Internal_Do_termEPost_u27e8___u27e9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__0_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 12,
    m_data: [
        116, 101, 114, 109, 69, 112, 111, 115, 116, 226, 159, 168, 95, 226, 159, 169, 0,
    ],
};
static mut l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__1_value)
            as *mut crate::leanh::LeanObject,
        1742885236933170401 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__2_value)
            as *mut crate::leanh::LeanObject,
        1237304041707523237 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__0_value)
            as *mut crate::leanh::LeanObject,
        5777631180175294420 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 6,
    m_data: [101, 112, 111, 115, 116, 226, 159, 168, 0],
};
static mut l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__4_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__15_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__5_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__18_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__6_value:
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
        core::ptr::addr_of!(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Internal_Do_termEpost_u27e8___u27e9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__0_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__3_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__5_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__5_value) as *mut crate::leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__4_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__5_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__7_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [69, 80, 111, 115, 116, 46, 99, 111, 110, 115, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 80, 111, 115, 116, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__10_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 110, 115, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__10_value) as *mut crate::leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value) as *mut crate::leanh::LeanObject,2065626917229203555 as *mut crate::leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__10_value) as *mut crate::leanh::LeanObject,7058350748084753084 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11_value) as *mut crate::leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__1_value) as *mut crate::leanh::LeanObject,1742885236933170401 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__2_value) as *mut crate::leanh::LeanObject,1237304041707523237 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value) as *mut crate::leanh::LeanObject,2177709115755977789 as *mut crate::leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__10_value) as *mut crate::leanh::LeanObject,17934775443570434810 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__13_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__14_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__12_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__15_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__14_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__16_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__13_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__15_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__18_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [69, 80, 111, 115, 116, 46, 110, 105, 108, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__20_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 105, 108, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__20_value) as *mut crate::leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value) as *mut crate::leanh::LeanObject,2065626917229203555 as *mut crate::leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__20_value) as *mut crate::leanh::LeanObject,9457925179424237236 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21_value) as *mut crate::leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__1_value) as *mut crate::leanh::LeanObject,1742885236933170401 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__2_value) as *mut crate::leanh::LeanObject,1237304041707523237 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value) as *mut crate::leanh::LeanObject,2177709115755977789 as *mut crate::leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__20_value) as *mut crate::leanh::LeanObject,2081293669908326466 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__23_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__24_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__22_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__25_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__24_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__26_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__23_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__25_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [69, 80, 111, 115, 116, 46, 99, 111, 110, 115, 46, 109, 107, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__2_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value) as *mut crate::leanh::LeanObject,2065626917229203555 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__10_value) as *mut crate::leanh::LeanObject,7058350748084753084 as *mut crate::leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__2_value) as *mut crate::leanh::LeanObject,8838583596811297908 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__1_value) as *mut crate::leanh::LeanObject,1742885236933170401 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__2_value) as *mut crate::leanh::LeanObject,1237304041707523237 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value) as *mut crate::leanh::LeanObject,2177709115755977789 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__10_value) as *mut crate::leanh::LeanObject,17934775443570434810 as *mut crate::leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__2_value) as *mut crate::leanh::LeanObject,8766565194230007434 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__6_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__9_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [69, 80, 111, 115, 116, 46, 110, 105, 108, 46, 109, 107, 0]};
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value) as *mut crate::leanh::LeanObject,2065626917229203555 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__20_value) as *mut crate::leanh::LeanObject,9457925179424237236 as *mut crate::leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__2_value) as *mut crate::leanh::LeanObject,11564427836094459164 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11_value) as *mut crate::leanh::LeanObject;
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__1_value) as *mut crate::leanh::LeanObject,1742885236933170401 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__2_value) as *mut crate::leanh::LeanObject,1237304041707523237 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__9_value) as *mut crate::leanh::LeanObject,2177709115755977789 as *mut crate::leanh::LeanObject] };
static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__20_value) as *mut crate::leanh::LeanObject,2081293669908326466 as *mut crate::leanh::LeanObject] };
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__2_value) as *mut crate::leanh::LeanObject,10550892441081213282 as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__13_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__14_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__12_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__15_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__14_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__16_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__13_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__15_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_unexpandEPostCons___closed__0_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [95, 102, 97, 107, 101, 77, 111, 100, 0],
};
static mut l_Std_Internal_Do_unexpandEPostCons___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_unexpandEPostCons___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_unexpandEPostCons___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Internal_Do_unexpandEPostCons___closed__0_value)
                as *mut crate::leanh::LeanObject,
            3838192344338869416 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Internal_Do_unexpandEPostCons___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_unexpandEPostCons___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Internal_Do_unexpandEPostCons___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_Do_unexpandEPostCons___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Internal_Do_unexpandEPostConsMk___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_Do_unexpandEPostConsMk___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_Internal_Do_EPost_nil_toCtorIdx(
    mut v_x_589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_590_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_590_;
}
pub unsafe fn _init_l_Std_Internal_Do_instPartialOrderNil() -> *mut crate::leanh::LeanObject {
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_591_ = crate::leanh::lean_box(0);
    return v___x_591_;
}
pub unsafe fn _init_l_Std_Internal_Do_instCompleteLatticeNil() -> *mut crate::leanh::LeanObject {
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_592_ = crate::leanh::lean_box(0);
    return v___x_592_;
}
pub unsafe fn l_Std_Internal_Do_instPartialOrderCons(
    mut v_eh_593_: *mut crate::leanh::LeanObject,
    mut v_et_594_: *mut crate::leanh::LeanObject,
    mut v_inst_595_: *mut crate::leanh::LeanObject,
    mut v_inst_596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_597_ = crate::leanh::lean_box(0);
    return v___x_597_;
}
pub unsafe fn l_Std_Internal_Do_instCompleteLatticeCons(
    mut v_eh_598_: *mut crate::leanh::LeanObject,
    mut v_et_599_: *mut crate::leanh::LeanObject,
    mut v_inst_600_: *mut crate::leanh::LeanObject,
    mut v_inst_601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_602_ = crate::leanh::lean_box(0);
    return v___x_602_;
}
pub unsafe fn _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_684_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__7;
    v___x_685_ = l_String_toRawSubstring_x27(v___x_684_);
    return v___x_685_;
}
pub unsafe fn _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_708_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_708_;
}
pub unsafe fn _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_710_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__18;
    v___x_711_ = l_String_toRawSubstring_x27(v___x_710_);
    return v___x_711_;
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1(
    mut v_x_733_: *mut crate::leanh::LeanObject,
    mut v_a_734_: *mut crate::leanh::LeanObject,
    mut v_a_735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: u8 = 0;
    v___x_736_ = l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4;
    crate::leanh::lean_inc(v_x_733_);
    v___x_737_ = l_Lean_Syntax_isOfKind(v_x_733_, v___x_736_);
    if v___x_737_ == 0 {
        let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_733_);
        v___x_738_ = crate::leanh::lean_box(1);
        v___x_739_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_739_, 0, v___x_738_);
        crate::leanh::lean_ctor_set(v___x_739_, 1, v_a_735_);
        return v___x_739_;
    } else {
        let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_743_: u8 = 0;
        v___x_740_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_741_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_742_ = l_Lean_Syntax_getArg(v_x_733_, v___x_741_);
        crate::leanh::lean_dec(v_x_733_);
        crate::leanh::lean_inc(v___x_742_);
        v___x_743_ = l_Lean_Syntax_matchesNull(v___x_742_, v___x_740_);
        if v___x_743_ == 0 {
            let mut v___x_744_: u8 = 0;
            crate::leanh::lean_inc(v___x_742_);
            v___x_744_ = l_Lean_Syntax_matchesNull(v___x_742_, v___x_741_);
            if v___x_744_ == 0 {
                let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_747_: u8 = 0;
                v___x_745_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_746_ = l_Lean_Syntax_getNumArgs(v___x_742_);
                v___x_747_ = lean_nat_dec_le(v___x_745_, v___x_746_);
                if v___x_747_ == 0 {
                    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_746_);
                    crate::leanh::lean_dec(v___x_742_);
                    v___x_748_ = crate::leanh::lean_box(1);
                    v___x_749_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_749_, 0, v___x_748_);
                    crate::leanh::lean_ctor_set(v___x_749_, 1, v_a_735_);
                    return v___x_749_;
                } else {
                    let mut v_quotContext_750_: *mut crate::leanh::LeanObject =
                        core::ptr::null_mut();
                    let mut v_currMacroScope_751_: *mut crate::leanh::LeanObject =
                        core::ptr::null_mut();
                    let mut v_ref_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v_quotContext_750_ = crate::leanh::lean_ctor_get(v_a_734_, 1);
                    v_currMacroScope_751_ = crate::leanh::lean_ctor_get(v_a_734_, 2);
                    v_ref_752_ = crate::leanh::lean_ctor_get(v_a_734_, 5);
                    v___x_753_ = l_Lean_Syntax_getArg(v___x_742_, v___x_740_);
                    v___x_754_ = l_Lean_Syntax_getArgs(v___x_742_);
                    crate::leanh::lean_dec(v___x_742_);
                    v___x_755_ = l_Array_extract___redArg(v___x_754_, v___x_745_, v___x_746_);
                    crate::leanh::lean_dec_ref(v___x_754_);
                    v___x_756_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1;
                    v___x_757_ = crate::leanh::lean_box(2);
                    v___x_758_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_758_, 0, v___x_757_);
                    crate::leanh::lean_ctor_set(v___x_758_, 1, v___x_756_);
                    crate::leanh::lean_ctor_set(v___x_758_, 2, v___x_755_);
                    v___x_759_ = l_Lean_Syntax_getArgs(v___x_758_);
                    crate::leanh::lean_dec_ref_known(v___x_758_, 3);
                    v___x_760_ = l_Lean_SourceInfo_fromRef(v_ref_752_, v___x_744_);
                    v___x_761_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6;
                    v___x_762_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8);
                    v___x_763_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11;
                    crate::leanh::lean_inc(v_currMacroScope_751_);
                    crate::leanh::lean_inc(v_quotContext_750_);
                    v___x_764_ =
                        l_Lean_addMacroScope(v_quotContext_750_, v___x_763_, v_currMacroScope_751_);
                    v___x_765_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__16;
                    crate::leanh::lean_inc_n(v___x_760_, 6);
                    v___x_766_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_766_, 0, v___x_760_);
                    crate::leanh::lean_ctor_set(v___x_766_, 1, v___x_762_);
                    crate::leanh::lean_ctor_set(v___x_766_, 2, v___x_764_);
                    crate::leanh::lean_ctor_set(v___x_766_, 3, v___x_765_);
                    v___x_767_ = l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7;
                    v___x_768_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_768_, 0, v___x_760_);
                    crate::leanh::lean_ctor_set(v___x_768_, 1, v___x_767_);
                    v___x_769_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17);
                    v___x_770_ = l_Array_append___redArg(v___x_769_, v___x_759_);
                    crate::leanh::lean_dec_ref(v___x_759_);
                    v___x_771_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_771_, 0, v___x_760_);
                    crate::leanh::lean_ctor_set(v___x_771_, 1, v___x_756_);
                    crate::leanh::lean_ctor_set(v___x_771_, 2, v___x_770_);
                    v___x_772_ = l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17;
                    v___x_773_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_773_, 0, v___x_760_);
                    crate::leanh::lean_ctor_set(v___x_773_, 1, v___x_772_);
                    v___x_774_ = l_Lean_Syntax_node3(
                        v___x_760_, v___x_736_, v___x_768_, v___x_771_, v___x_773_,
                    );
                    v___x_775_ =
                        l_Lean_Syntax_node2(v___x_760_, v___x_756_, v___x_753_, v___x_774_);
                    v___x_776_ =
                        l_Lean_Syntax_node2(v___x_760_, v___x_761_, v___x_766_, v___x_775_);
                    v___x_777_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_777_, 0, v___x_776_);
                    crate::leanh::lean_ctor_set(v___x_777_, 1, v_a_735_);
                    return v___x_777_;
                }
            } else {
                let mut v_quotContext_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_currMacroScope_779_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_ref_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_quotContext_778_ = crate::leanh::lean_ctor_get(v_a_734_, 1);
                v_currMacroScope_779_ = crate::leanh::lean_ctor_get(v_a_734_, 2);
                v_ref_780_ = crate::leanh::lean_ctor_get(v_a_734_, 5);
                v___x_781_ = l_Lean_Syntax_getArg(v___x_742_, v___x_740_);
                crate::leanh::lean_dec(v___x_742_);
                v___x_782_ = l_Lean_SourceInfo_fromRef(v_ref_780_, v___x_743_);
                v___x_783_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6;
                v___x_784_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8);
                v___x_785_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11;
                crate::leanh::lean_inc_n(v_currMacroScope_779_, 2);
                crate::leanh::lean_inc_n(v_quotContext_778_, 2);
                v___x_786_ =
                    l_Lean_addMacroScope(v_quotContext_778_, v___x_785_, v_currMacroScope_779_);
                v___x_787_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__16;
                crate::leanh::lean_inc_n(v___x_782_, 3);
                v___x_788_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_788_, 0, v___x_782_);
                crate::leanh::lean_ctor_set(v___x_788_, 1, v___x_784_);
                crate::leanh::lean_ctor_set(v___x_788_, 2, v___x_786_);
                crate::leanh::lean_ctor_set(v___x_788_, 3, v___x_787_);
                v___x_789_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1;
                v___x_790_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19);
                v___x_791_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21;
                v___x_792_ =
                    l_Lean_addMacroScope(v_quotContext_778_, v___x_791_, v_currMacroScope_779_);
                v___x_793_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__26;
                v___x_794_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_794_, 0, v___x_782_);
                crate::leanh::lean_ctor_set(v___x_794_, 1, v___x_790_);
                crate::leanh::lean_ctor_set(v___x_794_, 2, v___x_792_);
                crate::leanh::lean_ctor_set(v___x_794_, 3, v___x_793_);
                v___x_795_ = l_Lean_Syntax_node2(v___x_782_, v___x_789_, v___x_781_, v___x_794_);
                v___x_796_ = l_Lean_Syntax_node2(v___x_782_, v___x_783_, v___x_788_, v___x_795_);
                v___x_797_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_797_, 0, v___x_796_);
                crate::leanh::lean_ctor_set(v___x_797_, 1, v_a_735_);
                return v___x_797_;
            }
        } else {
            let mut v_quotContext_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ref_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_801_: u8 = 0;
            let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_742_);
            v_quotContext_798_ = crate::leanh::lean_ctor_get(v_a_734_, 1);
            v_currMacroScope_799_ = crate::leanh::lean_ctor_get(v_a_734_, 2);
            v_ref_800_ = crate::leanh::lean_ctor_get(v_a_734_, 5);
            v___x_801_ = 0;
            v___x_802_ = l_Lean_SourceInfo_fromRef(v_ref_800_, v___x_801_);
            v___x_803_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__19);
            v___x_804_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__21;
            crate::leanh::lean_inc(v_currMacroScope_799_);
            crate::leanh::lean_inc(v_quotContext_798_);
            v___x_805_ =
                l_Lean_addMacroScope(v_quotContext_798_, v___x_804_, v_currMacroScope_799_);
            v___x_806_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__26;
            v___x_807_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_807_, 0, v___x_802_);
            crate::leanh::lean_ctor_set(v___x_807_, 1, v___x_803_);
            crate::leanh::lean_ctor_set(v___x_807_, 2, v___x_805_);
            crate::leanh::lean_ctor_set(v___x_807_, 3, v___x_806_);
            v___x_808_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_808_, 0, v___x_807_);
            crate::leanh::lean_ctor_set(v___x_808_, 1, v_a_735_);
            return v___x_808_;
        }
    }
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___boxed(
    mut v_x_809_: *mut crate::leanh::LeanObject,
    mut v_a_810_: *mut crate::leanh::LeanObject,
    mut v_a_811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_812_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1(v_x_809_, v_a_810_, v_a_811_);
    crate::leanh::lean_dec_ref(v_a_810_);
    return v_res_812_;
}
pub unsafe fn _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_814_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__0;
    v___x_815_ = l_String_toRawSubstring_x27(v___x_814_);
    return v___x_815_;
}
pub unsafe fn _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_840_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__9;
    v___x_841_ = l_String_toRawSubstring_x27(v___x_840_);
    return v___x_841_;
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1(
    mut v_x_864_: *mut crate::leanh::LeanObject,
    mut v_a_865_: *mut crate::leanh::LeanObject,
    mut v_a_866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: u8 = 0;
    v___x_867_ = l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1;
    crate::leanh::lean_inc(v_x_864_);
    v___x_868_ = l_Lean_Syntax_isOfKind(v_x_864_, v___x_867_);
    if v___x_868_ == 0 {
        let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_864_);
        v___x_869_ = crate::leanh::lean_box(1);
        v___x_870_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_870_, 0, v___x_869_);
        crate::leanh::lean_ctor_set(v___x_870_, 1, v_a_866_);
        return v___x_870_;
    } else {
        let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_874_: u8 = 0;
        v___x_871_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_872_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_873_ = l_Lean_Syntax_getArg(v_x_864_, v___x_872_);
        crate::leanh::lean_dec(v_x_864_);
        crate::leanh::lean_inc(v___x_873_);
        v___x_874_ = l_Lean_Syntax_matchesNull(v___x_873_, v___x_871_);
        if v___x_874_ == 0 {
            let mut v___x_875_: u8 = 0;
            crate::leanh::lean_inc(v___x_873_);
            v___x_875_ = l_Lean_Syntax_matchesNull(v___x_873_, v___x_872_);
            if v___x_875_ == 0 {
                let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_878_: u8 = 0;
                v___x_876_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_877_ = l_Lean_Syntax_getNumArgs(v___x_873_);
                v___x_878_ = lean_nat_dec_le(v___x_876_, v___x_877_);
                if v___x_878_ == 0 {
                    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_877_);
                    crate::leanh::lean_dec(v___x_873_);
                    v___x_879_ = crate::leanh::lean_box(1);
                    v___x_880_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_880_, 0, v___x_879_);
                    crate::leanh::lean_ctor_set(v___x_880_, 1, v_a_866_);
                    return v___x_880_;
                } else {
                    let mut v_quotContext_881_: *mut crate::leanh::LeanObject =
                        core::ptr::null_mut();
                    let mut v_currMacroScope_882_: *mut crate::leanh::LeanObject =
                        core::ptr::null_mut();
                    let mut v_ref_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v_quotContext_881_ = crate::leanh::lean_ctor_get(v_a_865_, 1);
                    v_currMacroScope_882_ = crate::leanh::lean_ctor_get(v_a_865_, 2);
                    v_ref_883_ = crate::leanh::lean_ctor_get(v_a_865_, 5);
                    v___x_884_ = l_Lean_Syntax_getArg(v___x_873_, v___x_871_);
                    v___x_885_ = l_Lean_Syntax_getArgs(v___x_873_);
                    crate::leanh::lean_dec(v___x_873_);
                    v___x_886_ = l_Array_extract___redArg(v___x_885_, v___x_876_, v___x_877_);
                    crate::leanh::lean_dec_ref(v___x_885_);
                    v___x_887_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1;
                    v___x_888_ = crate::leanh::lean_box(2);
                    v___x_889_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_889_, 0, v___x_888_);
                    crate::leanh::lean_ctor_set(v___x_889_, 1, v___x_887_);
                    crate::leanh::lean_ctor_set(v___x_889_, 2, v___x_886_);
                    v___x_890_ = l_Lean_Syntax_getArgs(v___x_889_);
                    crate::leanh::lean_dec_ref_known(v___x_889_, 3);
                    v___x_891_ = l_Lean_SourceInfo_fromRef(v_ref_883_, v___x_875_);
                    v___x_892_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6;
                    v___x_893_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1);
                    v___x_894_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3;
                    crate::leanh::lean_inc(v_currMacroScope_882_);
                    crate::leanh::lean_inc(v_quotContext_881_);
                    v___x_895_ =
                        l_Lean_addMacroScope(v_quotContext_881_, v___x_894_, v_currMacroScope_882_);
                    v___x_896_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8;
                    crate::leanh::lean_inc_n(v___x_891_, 6);
                    v___x_897_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_897_, 0, v___x_891_);
                    crate::leanh::lean_ctor_set(v___x_897_, 1, v___x_893_);
                    crate::leanh::lean_ctor_set(v___x_897_, 2, v___x_895_);
                    crate::leanh::lean_ctor_set(v___x_897_, 3, v___x_896_);
                    v___x_898_ = l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2;
                    v___x_899_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_899_, 0, v___x_891_);
                    crate::leanh::lean_ctor_set(v___x_899_, 1, v___x_898_);
                    v___x_900_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17);
                    v___x_901_ = l_Array_append___redArg(v___x_900_, v___x_890_);
                    crate::leanh::lean_dec_ref(v___x_890_);
                    v___x_902_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_902_, 0, v___x_891_);
                    crate::leanh::lean_ctor_set(v___x_902_, 1, v___x_887_);
                    crate::leanh::lean_ctor_set(v___x_902_, 2, v___x_901_);
                    v___x_903_ = l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17;
                    v___x_904_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_904_, 0, v___x_891_);
                    crate::leanh::lean_ctor_set(v___x_904_, 1, v___x_903_);
                    v___x_905_ = l_Lean_Syntax_node3(
                        v___x_891_, v___x_867_, v___x_899_, v___x_902_, v___x_904_,
                    );
                    v___x_906_ =
                        l_Lean_Syntax_node2(v___x_891_, v___x_887_, v___x_884_, v___x_905_);
                    v___x_907_ =
                        l_Lean_Syntax_node2(v___x_891_, v___x_892_, v___x_897_, v___x_906_);
                    v___x_908_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_908_, 0, v___x_907_);
                    crate::leanh::lean_ctor_set(v___x_908_, 1, v_a_866_);
                    return v___x_908_;
                }
            } else {
                let mut v_quotContext_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_currMacroScope_910_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_ref_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_quotContext_909_ = crate::leanh::lean_ctor_get(v_a_865_, 1);
                v_currMacroScope_910_ = crate::leanh::lean_ctor_get(v_a_865_, 2);
                v_ref_911_ = crate::leanh::lean_ctor_get(v_a_865_, 5);
                v___x_912_ = l_Lean_Syntax_getArg(v___x_873_, v___x_871_);
                crate::leanh::lean_dec(v___x_873_);
                v___x_913_ = l_Lean_SourceInfo_fromRef(v_ref_911_, v___x_874_);
                v___x_914_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6;
                v___x_915_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1);
                v___x_916_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3;
                crate::leanh::lean_inc_n(v_currMacroScope_910_, 2);
                crate::leanh::lean_inc_n(v_quotContext_909_, 2);
                v___x_917_ =
                    l_Lean_addMacroScope(v_quotContext_909_, v___x_916_, v_currMacroScope_910_);
                v___x_918_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8;
                crate::leanh::lean_inc_n(v___x_913_, 3);
                v___x_919_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_919_, 0, v___x_913_);
                crate::leanh::lean_ctor_set(v___x_919_, 1, v___x_915_);
                crate::leanh::lean_ctor_set(v___x_919_, 2, v___x_917_);
                crate::leanh::lean_ctor_set(v___x_919_, 3, v___x_918_);
                v___x_920_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1;
                v___x_921_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10);
                v___x_922_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11;
                v___x_923_ =
                    l_Lean_addMacroScope(v_quotContext_909_, v___x_922_, v_currMacroScope_910_);
                v___x_924_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__16;
                v___x_925_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_925_, 0, v___x_913_);
                crate::leanh::lean_ctor_set(v___x_925_, 1, v___x_921_);
                crate::leanh::lean_ctor_set(v___x_925_, 2, v___x_923_);
                crate::leanh::lean_ctor_set(v___x_925_, 3, v___x_924_);
                v___x_926_ = l_Lean_Syntax_node2(v___x_913_, v___x_920_, v___x_912_, v___x_925_);
                v___x_927_ = l_Lean_Syntax_node2(v___x_913_, v___x_914_, v___x_919_, v___x_926_);
                v___x_928_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_928_, 0, v___x_927_);
                crate::leanh::lean_ctor_set(v___x_928_, 1, v_a_866_);
                return v___x_928_;
            }
        } else {
            let mut v_quotContext_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ref_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_932_: u8 = 0;
            let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_873_);
            v_quotContext_929_ = crate::leanh::lean_ctor_get(v_a_865_, 1);
            v_currMacroScope_930_ = crate::leanh::lean_ctor_get(v_a_865_, 2);
            v_ref_931_ = crate::leanh::lean_ctor_get(v_a_865_, 5);
            v___x_932_ = 0;
            v___x_933_ = l_Lean_SourceInfo_fromRef(v_ref_931_, v___x_932_);
            v___x_934_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__10);
            v___x_935_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__11;
            crate::leanh::lean_inc(v_currMacroScope_930_);
            crate::leanh::lean_inc(v_quotContext_929_);
            v___x_936_ =
                l_Lean_addMacroScope(v_quotContext_929_, v___x_935_, v_currMacroScope_930_);
            v___x_937_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__16;
            v___x_938_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_938_, 0, v___x_933_);
            crate::leanh::lean_ctor_set(v___x_938_, 1, v___x_934_);
            crate::leanh::lean_ctor_set(v___x_938_, 2, v___x_936_);
            crate::leanh::lean_ctor_set(v___x_938_, 3, v___x_937_);
            v___x_939_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_939_, 0, v___x_938_);
            crate::leanh::lean_ctor_set(v___x_939_, 1, v_a_866_);
            return v___x_939_;
        }
    }
}
pub unsafe fn l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___boxed(
    mut v_x_940_: *mut crate::leanh::LeanObject,
    mut v_a_941_: *mut crate::leanh::LeanObject,
    mut v_a_942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_943_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1(v_x_940_, v_a_941_, v_a_942_);
    crate::leanh::lean_dec_ref(v_a_941_);
    return v_res_943_;
}
pub unsafe fn l_Std_Internal_Do_unexpandEPostNil___redArg(
    mut v_a_944_: *mut crate::leanh::LeanObject,
    mut v_a_945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_946_: u8 = 0;
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_946_ = 0;
    v___x_947_ = l_Lean_SourceInfo_fromRef(v_a_944_, v___x_946_);
    v___x_948_ = l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4;
    v___x_949_ = l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7;
    crate::leanh::lean_inc_n(v___x_947_, 3);
    v___x_950_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_950_, 0, v___x_947_);
    crate::leanh::lean_ctor_set(v___x_950_, 1, v___x_949_);
    v___x_951_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1;
    v___x_952_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17);
    v___x_953_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_953_, 0, v___x_947_);
    crate::leanh::lean_ctor_set(v___x_953_, 1, v___x_951_);
    crate::leanh::lean_ctor_set(v___x_953_, 2, v___x_952_);
    v___x_954_ = l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17;
    v___x_955_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_955_, 0, v___x_947_);
    crate::leanh::lean_ctor_set(v___x_955_, 1, v___x_954_);
    v___x_956_ = l_Lean_Syntax_node3(v___x_947_, v___x_948_, v___x_950_, v___x_953_, v___x_955_);
    v___x_957_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_957_, 0, v___x_956_);
    crate::leanh::lean_ctor_set(v___x_957_, 1, v_a_945_);
    return v___x_957_;
}
pub unsafe fn l_Std_Internal_Do_unexpandEPostNil___redArg___boxed(
    mut v_a_958_: *mut crate::leanh::LeanObject,
    mut v_a_959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_960_ = l_Std_Internal_Do_unexpandEPostNil___redArg(v_a_958_, v_a_959_);
    crate::leanh::lean_dec(v_a_958_);
    return v_res_960_;
}
pub unsafe fn l_Std_Internal_Do_unexpandEPostNil(
    mut v_x_961_: *mut crate::leanh::LeanObject,
    mut v_a_962_: *mut crate::leanh::LeanObject,
    mut v_a_963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_964_ = l_Std_Internal_Do_unexpandEPostNil___redArg(v_a_962_, v_a_963_);
    return v___x_964_;
}
pub unsafe fn l_Std_Internal_Do_unexpandEPostNil___boxed(
    mut v_x_965_: *mut crate::leanh::LeanObject,
    mut v_a_966_: *mut crate::leanh::LeanObject,
    mut v_a_967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_968_ = l_Std_Internal_Do_unexpandEPostNil(v_x_965_, v_a_966_, v_a_967_);
    crate::leanh::lean_dec(v_a_966_);
    crate::leanh::lean_dec(v_x_965_);
    return v_res_968_;
}
pub unsafe fn _init_l_Std_Internal_Do_unexpandEPostCons___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_972_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_973_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__11;
    v___x_974_ = l_Std_Internal_Do_unexpandEPostCons___closed__1;
    v___x_975_ = l_Lean_addMacroScope(v___x_974_, v___x_973_, v___x_972_);
    return v___x_975_;
}
pub unsafe fn l_Std_Internal_Do_unexpandEPostCons(
    mut v_x_976_: *mut crate::leanh::LeanObject,
    mut v_a_977_: *mut crate::leanh::LeanObject,
    mut v_a_978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: u8 = 0;
    v___x_979_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6;
    crate::leanh::lean_inc(v_x_976_);
    v___x_980_ = l_Lean_Syntax_isOfKind(v_x_976_, v___x_979_);
    if v___x_980_ == 0 {
        let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_976_);
        v___x_981_ = crate::leanh::lean_box(0);
        v___x_982_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_982_, 0, v___x_981_);
        crate::leanh::lean_ctor_set(v___x_982_, 1, v_a_978_);
        return v___x_982_;
    } else {
        let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_986_: u8 = 0;
        v___x_983_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_984_ = l_Lean_Syntax_getArg(v_x_976_, v___x_983_);
        crate::leanh::lean_dec(v_x_976_);
        v___x_985_ = crate::leanh::lean_unsigned_to_nat(2);
        crate::leanh::lean_inc(v___x_984_);
        v___x_986_ = l_Lean_Syntax_matchesNull(v___x_984_, v___x_985_);
        if v___x_986_ == 0 {
            let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_984_);
            v___x_987_ = crate::leanh::lean_box(0);
            v___x_988_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_988_, 0, v___x_987_);
            crate::leanh::lean_ctor_set(v___x_988_, 1, v_a_978_);
            return v___x_988_;
        } else {
            let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_993_: u8 = 0;
            v___x_989_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_990_ = l_Lean_Syntax_getArg(v___x_984_, v___x_989_);
            v___x_991_ = l_Lean_Syntax_getArg(v___x_984_, v___x_983_);
            crate::leanh::lean_dec(v___x_984_);
            v___x_992_ = l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__4;
            crate::leanh::lean_inc(v___x_991_);
            v___x_993_ = l_Lean_Syntax_isOfKind(v___x_991_, v___x_992_);
            if v___x_993_ == 0 {
                let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_994_ = l_Lean_SourceInfo_fromRef(v_a_977_, v___x_993_);
                v___x_995_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8);
                v___x_996_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Internal_Do_unexpandEPostCons___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Internal_Do_unexpandEPostCons___closed__2_once),
                    _init_l_Std_Internal_Do_unexpandEPostCons___closed__2,
                );
                v___x_997_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__16;
                crate::leanh::lean_inc_n(v___x_994_, 2);
                v___x_998_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_998_, 0, v___x_994_);
                crate::leanh::lean_ctor_set(v___x_998_, 1, v___x_995_);
                crate::leanh::lean_ctor_set(v___x_998_, 2, v___x_996_);
                crate::leanh::lean_ctor_set(v___x_998_, 3, v___x_997_);
                v___x_999_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1;
                v___x_1000_ = l_Lean_Syntax_node2(v___x_994_, v___x_999_, v___x_990_, v___x_991_);
                v___x_1001_ = l_Lean_Syntax_node2(v___x_994_, v___x_979_, v___x_998_, v___x_1000_);
                v___x_1002_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1002_, 0, v___x_1001_);
                crate::leanh::lean_ctor_set(v___x_1002_, 1, v_a_978_);
                return v___x_1002_;
            } else {
                let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1004_: u8 = 0;
                v___x_1003_ = l_Lean_Syntax_getArg(v___x_991_, v___x_983_);
                crate::leanh::lean_inc(v___x_1003_);
                v___x_1004_ = l_Lean_Syntax_matchesNull(v___x_1003_, v___x_989_);
                if v___x_1004_ == 0 {
                    let mut v___x_1005_: u8 = 0;
                    crate::leanh::lean_inc(v___x_1003_);
                    v___x_1005_ = l_Lean_Syntax_matchesNull(v___x_1003_, v___x_983_);
                    if v___x_1005_ == 0 {
                        let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1007_: u8 = 0;
                        v___x_1006_ = l_Lean_Syntax_getNumArgs(v___x_1003_);
                        v___x_1007_ = lean_nat_dec_le(v___x_985_, v___x_1006_);
                        if v___x_1007_ == 0 {
                            let mut v___x_1008_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1009_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1010_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1011_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1012_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1013_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1014_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1015_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1016_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v___x_1006_);
                            crate::leanh::lean_dec(v___x_1003_);
                            v___x_1008_ = l_Lean_SourceInfo_fromRef(v_a_977_, v___x_1005_);
                            v___x_1009_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__8);
                            v___x_1010_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Std_Internal_Do_unexpandEPostCons___closed__2
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Std_Internal_Do_unexpandEPostCons___closed__2_once
                                ),
                                _init_l_Std_Internal_Do_unexpandEPostCons___closed__2,
                            );
                            v___x_1011_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__16;
                            crate::leanh::lean_inc_n(v___x_1008_, 2);
                            v___x_1012_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1012_, 0, v___x_1008_);
                            crate::leanh::lean_ctor_set(v___x_1012_, 1, v___x_1009_);
                            crate::leanh::lean_ctor_set(v___x_1012_, 2, v___x_1010_);
                            crate::leanh::lean_ctor_set(v___x_1012_, 3, v___x_1011_);
                            v___x_1013_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1;
                            v___x_1014_ = l_Lean_Syntax_node2(
                                v___x_1008_,
                                v___x_1013_,
                                v___x_990_,
                                v___x_991_,
                            );
                            v___x_1015_ = l_Lean_Syntax_node2(
                                v___x_1008_,
                                v___x_979_,
                                v___x_1012_,
                                v___x_1014_,
                            );
                            v___x_1016_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1016_, 0, v___x_1015_);
                            crate::leanh::lean_ctor_set(v___x_1016_, 1, v_a_978_);
                            return v___x_1016_;
                        } else {
                            let mut v___x_1017_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1018_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1019_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1020_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1021_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1022_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1023_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1024_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1025_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1026_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1027_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1028_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1029_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1030_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1031_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1032_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1033_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1034_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1035_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v___x_991_);
                            v___x_1017_ = l_Lean_Syntax_getArg(v___x_1003_, v___x_989_);
                            v___x_1018_ = l_Lean_Syntax_getArgs(v___x_1003_);
                            crate::leanh::lean_dec(v___x_1003_);
                            v___x_1019_ =
                                l_Array_extract___redArg(v___x_1018_, v___x_985_, v___x_1006_);
                            crate::leanh::lean_dec_ref(v___x_1018_);
                            v___x_1020_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1;
                            v___x_1021_ = crate::leanh::lean_box(2);
                            v___x_1022_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1022_, 0, v___x_1021_);
                            crate::leanh::lean_ctor_set(v___x_1022_, 1, v___x_1020_);
                            crate::leanh::lean_ctor_set(v___x_1022_, 2, v___x_1019_);
                            v___x_1023_ = l_Lean_Syntax_getArgs(v___x_1022_);
                            crate::leanh::lean_dec_ref_known(v___x_1022_, 3);
                            v___x_1024_ = l_Lean_SourceInfo_fromRef(v_a_977_, v___x_1005_);
                            v___x_1025_ = l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7;
                            crate::leanh::lean_inc_n(v___x_1024_, 4);
                            v___x_1026_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1026_, 0, v___x_1024_);
                            crate::leanh::lean_ctor_set(v___x_1026_, 1, v___x_1025_);
                            v___x_1027_ = l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12;
                            v___x_1028_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1028_, 0, v___x_1024_);
                            crate::leanh::lean_ctor_set(v___x_1028_, 1, v___x_1027_);
                            crate::leanh::lean_inc_ref(v___x_1028_);
                            v___x_1029_ = l_Array_mkArray4___redArg(
                                v___x_990_,
                                v___x_1028_,
                                v___x_1017_,
                                v___x_1028_,
                            );
                            v___x_1030_ = l_Array_append___redArg(v___x_1029_, v___x_1023_);
                            crate::leanh::lean_dec_ref(v___x_1023_);
                            v___x_1031_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1031_, 0, v___x_1024_);
                            crate::leanh::lean_ctor_set(v___x_1031_, 1, v___x_1020_);
                            crate::leanh::lean_ctor_set(v___x_1031_, 2, v___x_1030_);
                            v___x_1032_ = l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17;
                            v___x_1033_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1033_, 0, v___x_1024_);
                            crate::leanh::lean_ctor_set(v___x_1033_, 1, v___x_1032_);
                            v___x_1034_ = l_Lean_Syntax_node3(
                                v___x_1024_,
                                v___x_992_,
                                v___x_1026_,
                                v___x_1031_,
                                v___x_1033_,
                            );
                            v___x_1035_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1035_, 0, v___x_1034_);
                            crate::leanh::lean_ctor_set(v___x_1035_, 1, v_a_978_);
                            return v___x_1035_;
                        }
                    } else {
                        let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v___x_991_);
                        v___x_1036_ = l_Lean_Syntax_getArg(v___x_1003_, v___x_989_);
                        crate::leanh::lean_dec(v___x_1003_);
                        v___x_1037_ = l_Lean_SourceInfo_fromRef(v_a_977_, v___x_1004_);
                        v___x_1038_ = l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7;
                        crate::leanh::lean_inc_n(v___x_1037_, 4);
                        v___x_1039_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1039_, 0, v___x_1037_);
                        crate::leanh::lean_ctor_set(v___x_1039_, 1, v___x_1038_);
                        v___x_1040_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1;
                        v___x_1041_ = l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12;
                        v___x_1042_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1042_, 0, v___x_1037_);
                        crate::leanh::lean_ctor_set(v___x_1042_, 1, v___x_1041_);
                        v___x_1043_ = l_Lean_Syntax_node3(
                            v___x_1037_,
                            v___x_1040_,
                            v___x_990_,
                            v___x_1042_,
                            v___x_1036_,
                        );
                        v___x_1044_ = l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17;
                        v___x_1045_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1045_, 0, v___x_1037_);
                        crate::leanh::lean_ctor_set(v___x_1045_, 1, v___x_1044_);
                        v___x_1046_ = l_Lean_Syntax_node3(
                            v___x_1037_,
                            v___x_992_,
                            v___x_1039_,
                            v___x_1043_,
                            v___x_1045_,
                        );
                        v___x_1047_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1047_, 0, v___x_1046_);
                        crate::leanh::lean_ctor_set(v___x_1047_, 1, v_a_978_);
                        return v___x_1047_;
                    }
                } else {
                    let mut v___x_1048_: u8 = 0;
                    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_1003_);
                    crate::leanh::lean_dec(v___x_991_);
                    v___x_1048_ = 0;
                    v___x_1049_ = l_Lean_SourceInfo_fromRef(v_a_977_, v___x_1048_);
                    v___x_1050_ = l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__7;
                    crate::leanh::lean_inc_n(v___x_1049_, 3);
                    v___x_1051_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1051_, 0, v___x_1049_);
                    crate::leanh::lean_ctor_set(v___x_1051_, 1, v___x_1050_);
                    v___x_1052_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1;
                    v___x_1053_ = l_Lean_Syntax_node1(v___x_1049_, v___x_1052_, v___x_990_);
                    v___x_1054_ = l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17;
                    v___x_1055_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1055_, 0, v___x_1049_);
                    crate::leanh::lean_ctor_set(v___x_1055_, 1, v___x_1054_);
                    v___x_1056_ = l_Lean_Syntax_node3(
                        v___x_1049_,
                        v___x_992_,
                        v___x_1051_,
                        v___x_1053_,
                        v___x_1055_,
                    );
                    v___x_1057_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1057_, 0, v___x_1056_);
                    crate::leanh::lean_ctor_set(v___x_1057_, 1, v_a_978_);
                    return v___x_1057_;
                }
            }
        }
    }
}
pub unsafe fn l_Std_Internal_Do_unexpandEPostCons___boxed(
    mut v_x_1058_: *mut crate::leanh::LeanObject,
    mut v_a_1059_: *mut crate::leanh::LeanObject,
    mut v_a_1060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1061_ = l_Std_Internal_Do_unexpandEPostCons(v_x_1058_, v_a_1059_, v_a_1060_);
    crate::leanh::lean_dec(v_a_1059_);
    return v_res_1061_;
}
pub unsafe fn l_Std_Internal_Do_unexpandEPostNilMk___redArg(
    mut v_a_1062_: *mut crate::leanh::LeanObject,
    mut v_a_1063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1064_: u8 = 0;
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1064_ = 0;
    v___x_1065_ = l_Lean_SourceInfo_fromRef(v_a_1062_, v___x_1064_);
    v___x_1066_ = l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1;
    v___x_1067_ = l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2;
    crate::leanh::lean_inc_n(v___x_1065_, 3);
    v___x_1068_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1068_, 0, v___x_1065_);
    crate::leanh::lean_ctor_set(v___x_1068_, 1, v___x_1067_);
    v___x_1069_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1;
    v___x_1070_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__17);
    v___x_1071_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1071_, 0, v___x_1065_);
    crate::leanh::lean_ctor_set(v___x_1071_, 1, v___x_1069_);
    crate::leanh::lean_ctor_set(v___x_1071_, 2, v___x_1070_);
    v___x_1072_ = l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17;
    v___x_1073_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1073_, 0, v___x_1065_);
    crate::leanh::lean_ctor_set(v___x_1073_, 1, v___x_1072_);
    v___x_1074_ = l_Lean_Syntax_node3(
        v___x_1065_,
        v___x_1066_,
        v___x_1068_,
        v___x_1071_,
        v___x_1073_,
    );
    v___x_1075_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1075_, 0, v___x_1074_);
    crate::leanh::lean_ctor_set(v___x_1075_, 1, v_a_1063_);
    return v___x_1075_;
}
pub unsafe fn l_Std_Internal_Do_unexpandEPostNilMk___redArg___boxed(
    mut v_a_1076_: *mut crate::leanh::LeanObject,
    mut v_a_1077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1078_ = l_Std_Internal_Do_unexpandEPostNilMk___redArg(v_a_1076_, v_a_1077_);
    crate::leanh::lean_dec(v_a_1076_);
    return v_res_1078_;
}
pub unsafe fn l_Std_Internal_Do_unexpandEPostNilMk(
    mut v_x_1079_: *mut crate::leanh::LeanObject,
    mut v_a_1080_: *mut crate::leanh::LeanObject,
    mut v_a_1081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1082_ = l_Std_Internal_Do_unexpandEPostNilMk___redArg(v_a_1080_, v_a_1081_);
    return v___x_1082_;
}
pub unsafe fn l_Std_Internal_Do_unexpandEPostNilMk___boxed(
    mut v_x_1083_: *mut crate::leanh::LeanObject,
    mut v_a_1084_: *mut crate::leanh::LeanObject,
    mut v_a_1085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1086_ = l_Std_Internal_Do_unexpandEPostNilMk(v_x_1083_, v_a_1084_, v_a_1085_);
    crate::leanh::lean_dec(v_a_1084_);
    crate::leanh::lean_dec(v_x_1083_);
    return v_res_1086_;
}
pub unsafe fn _init_l_Std_Internal_Do_unexpandEPostConsMk___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1087_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1088_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__3;
    v___x_1089_ = l_Std_Internal_Do_unexpandEPostCons___closed__1;
    v___x_1090_ = l_Lean_addMacroScope(v___x_1089_, v___x_1088_, v___x_1087_);
    return v___x_1090_;
}
pub unsafe fn l_Std_Internal_Do_unexpandEPostConsMk(
    mut v_x_1091_: *mut crate::leanh::LeanObject,
    mut v_a_1092_: *mut crate::leanh::LeanObject,
    mut v_a_1093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: u8 = 0;
    v___x_1094_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__6;
    crate::leanh::lean_inc(v_x_1091_);
    v___x_1095_ = l_Lean_Syntax_isOfKind(v_x_1091_, v___x_1094_);
    if v___x_1095_ == 0 {
        let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1091_);
        v___x_1096_ = crate::leanh::lean_box(0);
        v___x_1097_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1097_, 0, v___x_1096_);
        crate::leanh::lean_ctor_set(v___x_1097_, 1, v_a_1093_);
        return v___x_1097_;
    } else {
        let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1101_: u8 = 0;
        v___x_1098_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1099_ = l_Lean_Syntax_getArg(v_x_1091_, v___x_1098_);
        crate::leanh::lean_dec(v_x_1091_);
        v___x_1100_ = crate::leanh::lean_unsigned_to_nat(2);
        crate::leanh::lean_inc(v___x_1099_);
        v___x_1101_ = l_Lean_Syntax_matchesNull(v___x_1099_, v___x_1100_);
        if v___x_1101_ == 0 {
            let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1099_);
            v___x_1102_ = crate::leanh::lean_box(0);
            v___x_1103_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1103_, 0, v___x_1102_);
            crate::leanh::lean_ctor_set(v___x_1103_, 1, v_a_1093_);
            return v___x_1103_;
        } else {
            let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1108_: u8 = 0;
            v___x_1104_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_1105_ = l_Lean_Syntax_getArg(v___x_1099_, v___x_1104_);
            v___x_1106_ = l_Lean_Syntax_getArg(v___x_1099_, v___x_1098_);
            crate::leanh::lean_dec(v___x_1099_);
            v___x_1107_ = l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__1;
            crate::leanh::lean_inc(v___x_1106_);
            v___x_1108_ = l_Lean_Syntax_isOfKind(v___x_1106_, v___x_1107_);
            if v___x_1108_ == 0 {
                let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1109_ = l_Lean_SourceInfo_fromRef(v_a_1092_, v___x_1108_);
                v___x_1110_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1);
                v___x_1111_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Internal_Do_unexpandEPostConsMk___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Internal_Do_unexpandEPostConsMk___closed__0_once),
                    _init_l_Std_Internal_Do_unexpandEPostConsMk___closed__0,
                );
                v___x_1112_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8;
                crate::leanh::lean_inc_n(v___x_1109_, 2);
                v___x_1113_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1113_, 0, v___x_1109_);
                crate::leanh::lean_ctor_set(v___x_1113_, 1, v___x_1110_);
                crate::leanh::lean_ctor_set(v___x_1113_, 2, v___x_1111_);
                crate::leanh::lean_ctor_set(v___x_1113_, 3, v___x_1112_);
                v___x_1114_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1;
                v___x_1115_ =
                    l_Lean_Syntax_node2(v___x_1109_, v___x_1114_, v___x_1105_, v___x_1106_);
                v___x_1116_ =
                    l_Lean_Syntax_node2(v___x_1109_, v___x_1094_, v___x_1113_, v___x_1115_);
                v___x_1117_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1117_, 0, v___x_1116_);
                crate::leanh::lean_ctor_set(v___x_1117_, 1, v_a_1093_);
                return v___x_1117_;
            } else {
                let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1119_: u8 = 0;
                v___x_1118_ = l_Lean_Syntax_getArg(v___x_1106_, v___x_1098_);
                crate::leanh::lean_inc(v___x_1118_);
                v___x_1119_ = l_Lean_Syntax_matchesNull(v___x_1118_, v___x_1104_);
                if v___x_1119_ == 0 {
                    let mut v___x_1120_: u8 = 0;
                    crate::leanh::lean_inc(v___x_1118_);
                    v___x_1120_ = l_Lean_Syntax_matchesNull(v___x_1118_, v___x_1098_);
                    if v___x_1120_ == 0 {
                        let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1122_: u8 = 0;
                        v___x_1121_ = l_Lean_Syntax_getNumArgs(v___x_1118_);
                        v___x_1122_ = lean_nat_dec_le(v___x_1100_, v___x_1121_);
                        if v___x_1122_ == 0 {
                            let mut v___x_1123_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1124_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1125_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1126_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1127_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1128_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1129_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1130_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1131_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v___x_1121_);
                            crate::leanh::lean_dec(v___x_1118_);
                            v___x_1123_ = l_Lean_SourceInfo_fromRef(v_a_1092_, v___x_1120_);
                            v___x_1124_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1), core::ptr::addr_of_mut!(l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1_once), _init_l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__1);
                            v___x_1125_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Std_Internal_Do_unexpandEPostConsMk___closed__0
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Std_Internal_Do_unexpandEPostConsMk___closed__0_once
                                ),
                                _init_l_Std_Internal_Do_unexpandEPostConsMk___closed__0,
                            );
                            v___x_1126_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEpost_u27e8___u27e9__1___closed__8;
                            crate::leanh::lean_inc_n(v___x_1123_, 2);
                            v___x_1127_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1127_, 0, v___x_1123_);
                            crate::leanh::lean_ctor_set(v___x_1127_, 1, v___x_1124_);
                            crate::leanh::lean_ctor_set(v___x_1127_, 2, v___x_1125_);
                            crate::leanh::lean_ctor_set(v___x_1127_, 3, v___x_1126_);
                            v___x_1128_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1;
                            v___x_1129_ = l_Lean_Syntax_node2(
                                v___x_1123_,
                                v___x_1128_,
                                v___x_1105_,
                                v___x_1106_,
                            );
                            v___x_1130_ = l_Lean_Syntax_node2(
                                v___x_1123_,
                                v___x_1094_,
                                v___x_1127_,
                                v___x_1129_,
                            );
                            v___x_1131_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1131_, 0, v___x_1130_);
                            crate::leanh::lean_ctor_set(v___x_1131_, 1, v_a_1093_);
                            return v___x_1131_;
                        } else {
                            let mut v___x_1132_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1133_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1134_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1135_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1136_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1137_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1138_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1139_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1140_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1141_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1142_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1143_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1144_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1145_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1146_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1147_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1148_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1149_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1150_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v___x_1106_);
                            v___x_1132_ = l_Lean_Syntax_getArg(v___x_1118_, v___x_1104_);
                            v___x_1133_ = l_Lean_Syntax_getArgs(v___x_1118_);
                            crate::leanh::lean_dec(v___x_1118_);
                            v___x_1134_ =
                                l_Array_extract___redArg(v___x_1133_, v___x_1100_, v___x_1121_);
                            crate::leanh::lean_dec_ref(v___x_1133_);
                            v___x_1135_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1;
                            v___x_1136_ = crate::leanh::lean_box(2);
                            v___x_1137_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1137_, 0, v___x_1136_);
                            crate::leanh::lean_ctor_set(v___x_1137_, 1, v___x_1135_);
                            crate::leanh::lean_ctor_set(v___x_1137_, 2, v___x_1134_);
                            v___x_1138_ = l_Lean_Syntax_getArgs(v___x_1137_);
                            crate::leanh::lean_dec_ref_known(v___x_1137_, 3);
                            v___x_1139_ = l_Lean_SourceInfo_fromRef(v_a_1092_, v___x_1120_);
                            v___x_1140_ = l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2;
                            crate::leanh::lean_inc_n(v___x_1139_, 4);
                            v___x_1141_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1141_, 0, v___x_1139_);
                            crate::leanh::lean_ctor_set(v___x_1141_, 1, v___x_1140_);
                            v___x_1142_ = l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12;
                            v___x_1143_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1143_, 0, v___x_1139_);
                            crate::leanh::lean_ctor_set(v___x_1143_, 1, v___x_1142_);
                            crate::leanh::lean_inc_ref(v___x_1143_);
                            v___x_1144_ = l_Array_mkArray4___redArg(
                                v___x_1105_,
                                v___x_1143_,
                                v___x_1132_,
                                v___x_1143_,
                            );
                            v___x_1145_ = l_Array_append___redArg(v___x_1144_, v___x_1138_);
                            crate::leanh::lean_dec_ref(v___x_1138_);
                            v___x_1146_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1146_, 0, v___x_1139_);
                            crate::leanh::lean_ctor_set(v___x_1146_, 1, v___x_1135_);
                            crate::leanh::lean_ctor_set(v___x_1146_, 2, v___x_1145_);
                            v___x_1147_ = l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17;
                            v___x_1148_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1148_, 0, v___x_1139_);
                            crate::leanh::lean_ctor_set(v___x_1148_, 1, v___x_1147_);
                            v___x_1149_ = l_Lean_Syntax_node3(
                                v___x_1139_,
                                v___x_1107_,
                                v___x_1141_,
                                v___x_1146_,
                                v___x_1148_,
                            );
                            v___x_1150_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1150_, 0, v___x_1149_);
                            crate::leanh::lean_ctor_set(v___x_1150_, 1, v_a_1093_);
                            return v___x_1150_;
                        }
                    } else {
                        let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v___x_1106_);
                        v___x_1151_ = l_Lean_Syntax_getArg(v___x_1118_, v___x_1104_);
                        crate::leanh::lean_dec(v___x_1118_);
                        v___x_1152_ = l_Lean_SourceInfo_fromRef(v_a_1092_, v___x_1119_);
                        v___x_1153_ = l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2;
                        crate::leanh::lean_inc_n(v___x_1152_, 4);
                        v___x_1154_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1154_, 0, v___x_1152_);
                        crate::leanh::lean_ctor_set(v___x_1154_, 1, v___x_1153_);
                        v___x_1155_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1;
                        v___x_1156_ = l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__12;
                        v___x_1157_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1157_, 0, v___x_1152_);
                        crate::leanh::lean_ctor_set(v___x_1157_, 1, v___x_1156_);
                        v___x_1158_ = l_Lean_Syntax_node3(
                            v___x_1152_,
                            v___x_1155_,
                            v___x_1105_,
                            v___x_1157_,
                            v___x_1151_,
                        );
                        v___x_1159_ = l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17;
                        v___x_1160_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1160_, 0, v___x_1152_);
                        crate::leanh::lean_ctor_set(v___x_1160_, 1, v___x_1159_);
                        v___x_1161_ = l_Lean_Syntax_node3(
                            v___x_1152_,
                            v___x_1107_,
                            v___x_1154_,
                            v___x_1158_,
                            v___x_1160_,
                        );
                        v___x_1162_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1162_, 0, v___x_1161_);
                        crate::leanh::lean_ctor_set(v___x_1162_, 1, v_a_1093_);
                        return v___x_1162_;
                    }
                } else {
                    let mut v___x_1163_: u8 = 0;
                    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_1118_);
                    crate::leanh::lean_dec(v___x_1106_);
                    v___x_1163_ = 0;
                    v___x_1164_ = l_Lean_SourceInfo_fromRef(v_a_1092_, v___x_1163_);
                    v___x_1165_ = l_Std_Internal_Do_termEpost_u27e8___u27e9___closed__2;
                    crate::leanh::lean_inc_n(v___x_1164_, 3);
                    v___x_1166_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1166_, 0, v___x_1164_);
                    crate::leanh::lean_ctor_set(v___x_1166_, 1, v___x_1165_);
                    v___x_1167_ = l_Std_Internal_Do___aux__Std__Internal__Do__ExceptPost______macroRules__Std__Internal__Do__termEPost_u27e8___u27e9__1___closed__1;
                    v___x_1168_ = l_Lean_Syntax_node1(v___x_1164_, v___x_1167_, v___x_1105_);
                    v___x_1169_ = l_Std_Internal_Do_termEPost_u27e8___u27e9___closed__17;
                    v___x_1170_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1170_, 0, v___x_1164_);
                    crate::leanh::lean_ctor_set(v___x_1170_, 1, v___x_1169_);
                    v___x_1171_ = l_Lean_Syntax_node3(
                        v___x_1164_,
                        v___x_1107_,
                        v___x_1166_,
                        v___x_1168_,
                        v___x_1170_,
                    );
                    v___x_1172_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1172_, 0, v___x_1171_);
                    crate::leanh::lean_ctor_set(v___x_1172_, 1, v_a_1093_);
                    return v___x_1172_;
                }
            }
        }
    }
}
pub unsafe fn l_Std_Internal_Do_unexpandEPostConsMk___boxed(
    mut v_x_1173_: *mut crate::leanh::LeanObject,
    mut v_a_1174_: *mut crate::leanh::LeanObject,
    mut v_a_1175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1176_ = l_Std_Internal_Do_unexpandEPostConsMk(v_x_1173_, v_a_1174_, v_a_1175_);
    crate::leanh::lean_dec(v_a_1174_);
    return v_res_1176_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_Do_ExceptPost(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Internal_Do_Assertion(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Internal_Do_instPartialOrderNil = _init_l_Std_Internal_Do_instPartialOrderNil();
    crate::leanh::lean_mark_persistent(l_Std_Internal_Do_instPartialOrderNil);
    l_Std_Internal_Do_instCompleteLatticeNil = _init_l_Std_Internal_Do_instCompleteLatticeNil();
    crate::leanh::lean_mark_persistent(l_Std_Internal_Do_instCompleteLatticeNil);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_Do_ExceptPost(
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
pub unsafe fn initialize_Std_Internal_Do_ExceptPost(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Internal_Do_Assertion(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Do_ExceptPost(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Internal_Do_ExceptPost(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Internal_Do_ExceptPost(builtin);
}
