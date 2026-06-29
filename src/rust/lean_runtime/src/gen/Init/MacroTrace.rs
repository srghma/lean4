// Lean compiler output
// Module: Init.MacroTrace
// Imports: Init.Meta Init.Notation Init.Data.ToString.Macro
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::Meta::Defs::{
    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f, l_Lean_Syntax_mkNameLit,
    l_Lean_TSyntax_getId, l_Lean_quoteNameMk,
};
use crate::r#gen::Init::Meta::{initialize_Init_Meta, runtime_initialize_Init_Meta};
use crate::r#gen::Init::Notation::{initialize_Init_Notation, runtime_initialize_Init_Notation};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_addMacroScope, l_String_toRawSubstring_x27,
    lean_erase_macro_scopes,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::{
    lean_string_append, lean_string_intercalate,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
pub static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__0_value:
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
static mut l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__1_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
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
        116, 101, 114, 109, 77, 97, 99, 114, 111, 46, 116, 114, 97, 99, 101, 91, 95, 93, 95, 0,
    ],
};
static mut l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__2_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__1_value)
            as *mut crate::leanh::LeanObject,
        8502785386346736171 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__3_value:
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
static mut l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__4_value: crate::leanh::LeanCtorObject<
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        12571085391447129896 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__5_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [77, 97, 99, 114, 111, 46, 116, 114, 97, 99, 101, 91, 0],
};
static mut l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__6_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__7_value:
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
    m_data: [105, 100, 101, 110, 116, 0],
};
static mut l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__8_value: crate::leanh::LeanCtorObject<
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__7_value)
            as *mut crate::leanh::LeanObject,
        5117844058249666356 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__9_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__10_value:
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
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__11_value:
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
    m_data: [93, 0],
};
static mut l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__12_value:
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
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__11_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__13_value:
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
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__10_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__14_value:
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
        105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 0,
    ],
};
static mut l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__15_value:
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
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__14_value)
            as *mut crate::leanh::LeanObject,
        18163029821153688220 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__16_value:
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
static mut l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__17_value:
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
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__16_value)
            as *mut crate::leanh::LeanObject,
        8609355255726335675 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__18_value:
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
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__17_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__19_value:
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
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__15_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__18_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__20_value:
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
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__13_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__19_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__21_value:
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
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__2_value)
            as *mut crate::leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__20_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_termMacro_x2etrace_x5b___x5d__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__2_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__4_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [77, 97, 99, 114, 111, 46, 116, 114, 97, 99, 101, 0]};
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__6_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [77, 97, 99, 114, 111, 0]};
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__7_value) as *mut crate::leanh::LeanObject;
static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__6_value) as *mut crate::leanh::LeanObject,14665357199263665561 as *mut crate::leanh::LeanObject] };
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__7_value) as *mut crate::leanh::LeanObject,9571542765358515358 as *mut crate::leanh::LeanObject] };
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__8_value) as *mut crate::leanh::LeanObject;
static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__6_value) as *mut crate::leanh::LeanObject,18105168627502861736 as *mut crate::leanh::LeanObject] };
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__7_value) as *mut crate::leanh::LeanObject,2130297764616213731 as *mut crate::leanh::LeanObject] };
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__10_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__9_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__12_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__12_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__14_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__14_value) as *mut crate::leanh::LeanObject;
static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__15_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__15_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__15_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__15_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__15_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__14_value) as *mut crate::leanh::LeanObject,7932075773091973500 as *mut crate::leanh::LeanObject] };
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__16_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__16_value) as *mut crate::leanh::LeanObject;
static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__17_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__17_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__17_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__17_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__17_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__16_value) as *mut crate::leanh::LeanObject,7306243862518720553 as *mut crate::leanh::LeanObject] };
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__18_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__19_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__19_value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__21_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__21_value) as *mut crate::leanh::LeanObject;
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__22_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__22: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__23_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__24_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__23_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__25_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__24_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__26_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 83, 33, 95, 0]};
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__27_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__26_value) as *mut crate::leanh::LeanObject,11081549158230622750 as *mut crate::leanh::LeanObject] };
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__28_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [115, 33, 0]};
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__29_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__30_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0]};
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__30_value) as *mut crate::leanh::LeanObject;
static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__31_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__31_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__31_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__31_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__31_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__31_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__31_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__30_value) as *mut crate::leanh::LeanObject,9368229134555052249 as *mut crate::leanh::LeanObject] };
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__31_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__32_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__32_value) as *mut crate::leanh::LeanObject;
pub static l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__33_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__33_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_241_ = l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__4;
    v___x_242_ = l_String_toRawSubstring_x27(v___x_241_);
    return v___x_242_;
}
pub unsafe fn _init_l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_278_ = l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__21;
    v___x_279_ = l_String_toRawSubstring_x27(v___x_278_);
    return v___x_279_;
}
pub unsafe fn l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1(
    mut v_x_300_: *mut crate::leanh::LeanObject,
    mut v_a_301_: *mut crate::leanh::LeanObject,
    mut v_a_302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_304_: u8 = 0;
    let mut v___x_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: u8 = 0;
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_303_ = l_Lean_termMacro_x2etrace_x5b___x5d___00__closed__2;
                crate::leanh::lean_inc(v_x_300_);
                v___x_304_ = l_Lean_Syntax_isOfKind(v_x_300_, v___x_303_);
                if v___x_304_ == 0 {
                    crate::leanh::lean_dec(v_x_300_);
                    v___x_305_ = crate::leanh::lean_box(1);
                    v___x_306_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_306_, 0, v___x_305_);
                    crate::leanh::lean_ctor_set(v___x_306_, 1, v_a_302_);
                    return v___x_306_;
                } else {
                    v_quotContext_307_ = crate::leanh::lean_ctor_get(v_a_301_, 1);
                    v_currMacroScope_308_ = crate::leanh::lean_ctor_get(v_a_301_, 2);
                    v_ref_309_ = crate::leanh::lean_ctor_get(v_a_301_, 5);
                    v___x_310_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_id_311_ = l_Lean_Syntax_getArg(v_x_300_, v___x_310_);
                    v___x_312_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_313_ = l_Lean_Syntax_getArg(v_x_300_, v___x_312_);
                    crate::leanh::lean_dec(v_x_300_);
                    v___x_314_ = 0;
                    v___x_315_ = l_Lean_SourceInfo_fromRef(v_ref_309_, v___x_314_);
                    v___x_316_ = l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__3;
                    v___x_317_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__5), core::ptr::addr_of_mut!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__5_once), _init_l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__5);
                    v___x_318_ = l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__8;
                    crate::leanh::lean_inc(v_currMacroScope_308_);
                    crate::leanh::lean_inc(v_quotContext_307_);
                    v___x_319_ =
                        l_Lean_addMacroScope(v_quotContext_307_, v___x_318_, v_currMacroScope_308_);
                    v___x_320_ = crate::leanh::lean_box(0);
                    v___x_321_ = l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__11;
                    crate::leanh::lean_inc(v___x_315_);
                    v___x_322_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_322_, 0, v___x_315_);
                    crate::leanh::lean_ctor_set(v___x_322_, 1, v___x_317_);
                    crate::leanh::lean_ctor_set(v___x_322_, 2, v___x_319_);
                    crate::leanh::lean_ctor_set(v___x_322_, 3, v___x_321_);
                    v___x_323_ = l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__13;
                    v___x_348_ = l_Lean_TSyntax_getId(v_id_311_);
                    crate::leanh::lean_dec(v_id_311_);
                    v___x_349_ = lean_erase_macro_scopes(v___x_348_);
                    crate::leanh::lean_inc(v___x_349_);
                    v___x_350_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                        v___x_320_, v___x_349_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_350_) == 0 {
                        v___x_351_ = l_Lean_quoteNameMk(v___x_349_);
                        v___y_325_ = v___x_351_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_349_);
                        v_val_352_ = crate::leanh::lean_ctor_get(v___x_350_, 0);
                        crate::leanh::lean_inc(v_val_352_);
                        crate::leanh::lean_dec_ref_known(v___x_350_, 1);
                        v___x_353_ = l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__31;
                        v___x_354_ = l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__32;
                        v___x_355_ = l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__33;
                        v___x_356_ = lean_string_intercalate(v___x_355_, v_val_352_);
                        v___x_357_ = lean_string_append(v___x_354_, v___x_356_);
                        crate::leanh::lean_dec_ref(v___x_356_);
                        v___x_358_ = crate::leanh::lean_box(2);
                        v___x_359_ = l_Lean_Syntax_mkNameLit(v___x_357_, v___x_358_);
                        v___x_360_ = lean_mk_empty_array_with_capacity(v___x_310_);
                        v___x_361_ = lean_array_push(v___x_360_, v___x_359_);
                        v___x_362_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_362_, 0, v___x_358_);
                        crate::leanh::lean_ctor_set(v___x_362_, 1, v___x_353_);
                        crate::leanh::lean_ctor_set(v___x_362_, 2, v___x_361_);
                        v___y_325_ = v___x_362_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_326_ = l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__15;
                v___x_327_ = l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__17;
                v___x_328_ = l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__18;
                crate::leanh::lean_inc_n(v___x_315_, 9);
                v___x_329_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_329_, 0, v___x_315_);
                crate::leanh::lean_ctor_set(v___x_329_, 1, v___x_328_);
                v___x_330_ = l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__20;
                v___x_331_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__22), core::ptr::addr_of_mut!(l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__22_once), _init_l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__22);
                v___x_332_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_currMacroScope_308_);
                crate::leanh::lean_inc(v_quotContext_307_);
                v___x_333_ =
                    l_Lean_addMacroScope(v_quotContext_307_, v___x_332_, v_currMacroScope_308_);
                v___x_334_ = l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__25;
                v___x_335_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_335_, 0, v___x_315_);
                crate::leanh::lean_ctor_set(v___x_335_, 1, v___x_331_);
                crate::leanh::lean_ctor_set(v___x_335_, 2, v___x_333_);
                crate::leanh::lean_ctor_set(v___x_335_, 3, v___x_334_);
                v___x_336_ = l_Lean_Syntax_node1(v___x_315_, v___x_330_, v___x_335_);
                v___x_337_ = l_Lean_Syntax_node2(v___x_315_, v___x_327_, v___x_329_, v___x_336_);
                v___x_338_ = l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__27;
                v___x_339_ = l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__28;
                v___x_340_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_340_, 0, v___x_315_);
                crate::leanh::lean_ctor_set(v___x_340_, 1, v___x_339_);
                v___x_341_ = l_Lean_Syntax_node2(v___x_315_, v___x_338_, v___x_340_, v___x_313_);
                v___x_342_ = l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___closed__29;
                v___x_343_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_343_, 0, v___x_315_);
                crate::leanh::lean_ctor_set(v___x_343_, 1, v___x_342_);
                v___x_344_ =
                    l_Lean_Syntax_node3(v___x_315_, v___x_326_, v___x_337_, v___x_341_, v___x_343_);
                v___x_345_ = l_Lean_Syntax_node2(v___x_315_, v___x_323_, v___y_325_, v___x_344_);
                v___x_346_ = l_Lean_Syntax_node2(v___x_315_, v___x_316_, v___x_322_, v___x_345_);
                v___x_347_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_347_, 0, v___x_346_);
                crate::leanh::lean_ctor_set(v___x_347_, 1, v_a_302_);
                return v___x_347_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1___boxed(
    mut v_x_363_: *mut crate::leanh::LeanObject,
    mut v_a_364_: *mut crate::leanh::LeanObject,
    mut v_a_365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_366_ =
        l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1(
            v_x_363_, v_a_364_, v_a_365_,
        );
    crate::leanh::lean_dec_ref(v_a_364_);
    return v_res_366_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_MacroTrace(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_MacroTrace(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_MacroTrace(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_MacroTrace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_MacroTrace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_MacroTrace(builtin);
}
