// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Entails
// Imports: Init.PropLemmas
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_addMacroScope, l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::PropLemmas::{
    initialize_Init_PropLemmas, runtime_initialize_Init_PropLemmas,
};
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__0_value:
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
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__1_value:
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
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__2_value:
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
    m_data: [66, 86, 68, 101, 99, 105, 100, 101, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__3_value:
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
    m_data: [76, 82, 65, 84, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__4_value:
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
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__5_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 7,
    m_data: [116, 101, 114, 109, 95, 226, 138, 168, 95, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__5_value)
        as *mut leanh::LeanObject;
static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_1:
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
            l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__1_value)
            as *mut leanh::LeanObject,
        5139300886809190733 as *mut leanh::LeanObject,
    ],
};
static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_2:
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
            l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__2_value)
            as *mut leanh::LeanObject,
        17363264175708149920 as *mut leanh::LeanObject,
    ],
};
static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_3:
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
            l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__3_value)
            as *mut leanh::LeanObject,
        14108742078913166941 as *mut leanh::LeanObject,
    ],
};
static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_4:
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
            l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_3
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__4_value)
            as *mut leanh::LeanObject,
        16855598961848779312 as *mut leanh::LeanObject,
    ],
};
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value:
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
            l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_4
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__5_value)
            as *mut leanh::LeanObject,
        9107789374283114430 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__7_value:
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
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__8_value:
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
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__7_value)
            as *mut leanh::LeanObject,
        12571085391447129896 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__9_value:
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
    m_data: [32, 226, 138, 168, 32, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__10_value:
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
        l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__9_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__11_value:
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
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__12_value:
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
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__11_value)
            as *mut leanh::LeanObject,
        8609355255726335675 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__13_value:
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
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__12_value)
            as *mut leanh::LeanObject,
        (((26 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__14_value:
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
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__10_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__13_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__15_value:
    leanh::LeanCtorObject<4> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value)
            as *mut leanh::LeanObject,
        (((25 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((26 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__14_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__15_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__3_value) as *mut leanh::LeanObject;
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__3_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__5_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [69, 110, 116, 97, 105, 108, 115, 46, 101, 118, 97, 108, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__5_value) as *mut leanh::LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__7_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [69, 110, 116, 97, 105, 108, 115, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__8_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [101, 118, 97, 108, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__8_value) as *mut leanh::LeanObject;
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__7_value) as *mut leanh::LeanObject,6742649520003532491 as *mut leanh::LeanObject] };
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__8_value) as *mut leanh::LeanObject,899181493805419292 as *mut leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__9_value) as *mut leanh::LeanObject;
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__3_value) as *mut leanh::LeanObject,14108742078913166941 as *mut leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__4_value) as *mut leanh::LeanObject,16855598961848779312 as *mut leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_5: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__7_value) as *mut leanh::LeanObject,9209341331324411620 as *mut leanh::LeanObject] };
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_5) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__8_value) as *mut leanh::LeanObject,7561698742759983679 as *mut leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__11_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__12_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__11_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__13_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__13_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__0_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__0_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 7,
    m_data: [116, 101, 114, 109, 95, 226, 138, 173, 95, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_1:
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
            l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__1_value)
            as *mut leanh::LeanObject,
        5139300886809190733 as *mut leanh::LeanObject,
    ],
};
static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_2:
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
            l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__2_value)
            as *mut leanh::LeanObject,
        17363264175708149920 as *mut leanh::LeanObject,
    ],
};
static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_3:
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
            l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__3_value)
            as *mut leanh::LeanObject,
        14108742078913166941 as *mut leanh::LeanObject,
    ],
};
static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_4:
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
            l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_3
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__4_value)
            as *mut leanh::LeanObject,
        16855598961848779312 as *mut leanh::LeanObject,
    ],
};
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value:
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
            l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_4
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__0_value)
            as *mut leanh::LeanObject,
        3721930517597245316 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__2_value:
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
    m_data: [32, 226, 138, 173, 32, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__3_value:
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
        l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__2_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__4_value:
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
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__12_value)
            as *mut leanh::LeanObject,
        (((30 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__5_value:
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
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__6_value:
    leanh::LeanCtorObject<4> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value)
            as *mut leanh::LeanObject,
        (((25 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((25 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 6, m_data: [116, 101, 114, 109, 194, 172, 95, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__0_value) as *mut leanh::LeanObject,17055224711078181598 as *mut leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__2_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 1, m_data: [194, 172, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__3_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__3_value) as *mut leanh::LeanObject;
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__3_value) as *mut leanh::LeanObject,7932075773091973500 as *mut leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__5_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__5_value) as *mut leanh::LeanObject;
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__5_value) as *mut leanh::LeanObject,7306243862518720553 as *mut leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__7_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__8_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__8_value) as *mut leanh::LeanObject,9871775667037945883 as *mut leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__10_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__10_value) as *mut leanh::LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__3_value) as *mut leanh::LeanObject,14108742078913166941 as *mut leanh::LeanObject] };
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__4_value) as *mut leanh::LeanObject,16855598961848779312 as *mut leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__13_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value) as *mut leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__14_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__13_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__15_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__15_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__16_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__15_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__16_value) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__17_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__17_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_294_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__5;
    v___x_295_ = l_String_toRawSubstring_x27(v___x_294_);
    return v___x_295_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1(
    mut v_x_318_: *mut leanh::LeanObject,
    mut v_a_319_: *mut leanh::LeanObject,
    mut v_a_320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: u8 = 0;
    v___x_321_ = l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6;
    leanh::lean_inc(v_x_318_);
    v___x_322_ = l_Lean_Syntax_isOfKind(v_x_318_, v___x_321_);
    if v___x_322_ == 0 {
        let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_318_);
        v___x_323_ = leanh::lean_box(1);
        v___x_324_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_324_, 0, v___x_323_);
        leanh::lean_ctor_set(v___x_324_, 1, v_a_320_);
        return v___x_324_;
    } else {
        let mut v_quotContext_325_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_326_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_327_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_332_: u8 = 0;
        let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_337_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_325_ = leanh::lean_ctor_get(v_a_319_, 1);
        v_currMacroScope_326_ = leanh::lean_ctor_get(v_a_319_, 2);
        v_ref_327_ = leanh::lean_ctor_get(v_a_319_, 5);
        v___x_328_ = leanh::lean_unsigned_to_nat(0);
        v___x_329_ = l_Lean_Syntax_getArg(v_x_318_, v___x_328_);
        v___x_330_ = leanh::lean_unsigned_to_nat(2);
        v___x_331_ = l_Lean_Syntax_getArg(v_x_318_, v___x_330_);
        leanh::lean_dec(v_x_318_);
        v___x_332_ = 0;
        v___x_333_ = l_Lean_SourceInfo_fromRef(v_ref_327_, v___x_332_);
        v___x_334_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4;
        v___x_335_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6_once), _init_l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6);
        v___x_336_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__9;
        leanh::lean_inc(v_currMacroScope_326_);
        leanh::lean_inc(v_quotContext_325_);
        v___x_337_ = l_Lean_addMacroScope(v_quotContext_325_, v___x_336_, v_currMacroScope_326_);
        v___x_338_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__12;
        leanh::lean_inc_n(v___x_333_, 2);
        v___x_339_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_339_, 0, v___x_333_);
        leanh::lean_ctor_set(v___x_339_, 1, v___x_335_);
        leanh::lean_ctor_set(v___x_339_, 2, v___x_337_);
        leanh::lean_ctor_set(v___x_339_, 3, v___x_338_);
        v___x_340_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__14;
        v___x_341_ = l_Lean_Syntax_node2(v___x_333_, v___x_340_, v___x_329_, v___x_331_);
        v___x_342_ = l_Lean_Syntax_node2(v___x_333_, v___x_334_, v___x_339_, v___x_341_);
        v___x_343_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_343_, 0, v___x_342_);
        leanh::lean_ctor_set(v___x_343_, 1, v_a_320_);
        return v___x_343_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___boxed(
    mut v_x_344_: *mut leanh::LeanObject,
    mut v_a_345_: *mut leanh::LeanObject,
    mut v_a_346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_347_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1(v_x_344_, v_a_345_, v_a_346_);
    leanh::lean_dec_ref(v_a_345_);
    return v_res_347_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1(
    mut v_x_351_: *mut leanh::LeanObject,
    mut v_a_352_: *mut leanh::LeanObject,
    mut v_a_353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: u8 = 0;
    v___x_354_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4;
    leanh::lean_inc(v_x_351_);
    v___x_355_ = l_Lean_Syntax_isOfKind(v_x_351_, v___x_354_);
    if v___x_355_ == 0 {
        let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_351_);
        v___x_356_ = leanh::lean_box(0);
        v___x_357_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_357_, 0, v___x_356_);
        leanh::lean_ctor_set(v___x_357_, 1, v_a_353_);
        return v___x_357_;
    } else {
        let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_361_: u8 = 0;
        v___x_358_ = leanh::lean_unsigned_to_nat(0);
        v___x_359_ = l_Lean_Syntax_getArg(v_x_351_, v___x_358_);
        v___x_360_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__1;
        leanh::lean_inc(v___x_359_);
        v___x_361_ = l_Lean_Syntax_isOfKind(v___x_359_, v___x_360_);
        if v___x_361_ == 0 {
            let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_359_);
            leanh::lean_dec(v_x_351_);
            v___x_362_ = leanh::lean_box(0);
            v___x_363_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_363_, 0, v___x_362_);
            leanh::lean_ctor_set(v___x_363_, 1, v_a_353_);
            return v___x_363_;
        } else {
            let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_367_: u8 = 0;
            v___x_364_ = leanh::lean_unsigned_to_nat(1);
            v___x_365_ = l_Lean_Syntax_getArg(v_x_351_, v___x_364_);
            leanh::lean_dec(v_x_351_);
            v___x_366_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_365_);
            v___x_367_ = l_Lean_Syntax_matchesNull(v___x_365_, v___x_366_);
            if v___x_367_ == 0 {
                let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_365_);
                leanh::lean_dec(v___x_359_);
                v___x_368_ = leanh::lean_box(0);
                v___x_369_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_369_, 0, v___x_368_);
                leanh::lean_ctor_set(v___x_369_, 1, v_a_353_);
                return v___x_369_;
            } else {
                let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_372_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_373_: u8 = 0;
                let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_370_ = l_Lean_Syntax_getArg(v___x_365_, v___x_358_);
                v___x_371_ = l_Lean_Syntax_getArg(v___x_365_, v___x_364_);
                leanh::lean_dec(v___x_365_);
                v_ref_372_ = l_Lean_replaceRef(v___x_359_, v_a_352_);
                leanh::lean_dec(v___x_359_);
                v___x_373_ = 0;
                v___x_374_ = l_Lean_SourceInfo_fromRef(v_ref_372_, v___x_373_);
                leanh::lean_dec(v_ref_372_);
                v___x_375_ = l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6;
                v___x_376_ = l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__9;
                leanh::lean_inc(v___x_374_);
                v___x_377_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_377_, 0, v___x_374_);
                leanh::lean_ctor_set(v___x_377_, 1, v___x_376_);
                v___x_378_ =
                    l_Lean_Syntax_node3(v___x_374_, v___x_375_, v___x_370_, v___x_377_, v___x_371_);
                v___x_379_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_379_, 0, v___x_378_);
                leanh::lean_ctor_set(v___x_379_, 1, v_a_353_);
                return v___x_379_;
            }
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___boxed(
    mut v_x_380_: *mut leanh::LeanObject,
    mut v_a_381_: *mut leanh::LeanObject,
    mut v_a_382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_383_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1(v_x_380_, v_a_381_, v_a_382_);
    leanh::lean_dec(v_a_381_);
    return v_res_383_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_428_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__10;
    v___x_429_ = l_String_toRawSubstring_x27(v___x_428_);
    return v___x_429_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1(
    mut v_x_448_: *mut leanh::LeanObject,
    mut v_a_449_: *mut leanh::LeanObject,
    mut v_a_450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: u8 = 0;
    v___x_451_ = l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1;
    leanh::lean_inc(v_x_448_);
    v___x_452_ = l_Lean_Syntax_isOfKind(v_x_448_, v___x_451_);
    if v___x_452_ == 0 {
        let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_454_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_448_);
        v___x_453_ = leanh::lean_box(1);
        v___x_454_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_454_, 0, v___x_453_);
        leanh::lean_ctor_set(v___x_454_, 1, v_a_450_);
        return v___x_454_;
    } else {
        let mut v_quotContext_455_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_456_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_457_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_462_: u8 = 0;
        let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_465_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_469_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_455_ = leanh::lean_ctor_get(v_a_449_, 1);
        v_currMacroScope_456_ = leanh::lean_ctor_get(v_a_449_, 2);
        v_ref_457_ = leanh::lean_ctor_get(v_a_449_, 5);
        v___x_458_ = leanh::lean_unsigned_to_nat(0);
        v___x_459_ = l_Lean_Syntax_getArg(v_x_448_, v___x_458_);
        v___x_460_ = leanh::lean_unsigned_to_nat(2);
        v___x_461_ = l_Lean_Syntax_getArg(v_x_448_, v___x_460_);
        leanh::lean_dec(v_x_448_);
        v___x_462_ = 0;
        v___x_463_ = l_Lean_SourceInfo_fromRef(v_ref_457_, v___x_462_);
        v___x_464_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__1;
        v___x_465_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__2;
        leanh::lean_inc_n(v___x_463_, 10);
        v___x_466_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_466_, 0, v___x_463_);
        leanh::lean_ctor_set(v___x_466_, 1, v___x_465_);
        v___x_467_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4;
        v___x_468_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6;
        v___x_469_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__7;
        v___x_470_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_470_, 0, v___x_463_);
        leanh::lean_ctor_set(v___x_470_, 1, v___x_469_);
        v___x_471_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__9;
        v___x_472_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__11), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__11_once), _init_l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__11);
        v___x_473_ = leanh::lean_box(0);
        leanh::lean_inc_n(v_currMacroScope_456_, 2);
        leanh::lean_inc_n(v_quotContext_455_, 2);
        v___x_474_ = l_Lean_addMacroScope(v_quotContext_455_, v___x_473_, v_currMacroScope_456_);
        v___x_475_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__14;
        v___x_476_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_476_, 0, v___x_463_);
        leanh::lean_ctor_set(v___x_476_, 1, v___x_472_);
        leanh::lean_ctor_set(v___x_476_, 2, v___x_474_);
        leanh::lean_ctor_set(v___x_476_, 3, v___x_475_);
        v___x_477_ = l_Lean_Syntax_node1(v___x_463_, v___x_471_, v___x_476_);
        v___x_478_ = l_Lean_Syntax_node2(v___x_463_, v___x_468_, v___x_470_, v___x_477_);
        v___x_479_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4;
        v___x_480_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6_once), _init_l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6);
        v___x_481_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__9;
        v___x_482_ = l_Lean_addMacroScope(v_quotContext_455_, v___x_481_, v_currMacroScope_456_);
        v___x_483_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__16;
        v___x_484_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_484_, 0, v___x_463_);
        leanh::lean_ctor_set(v___x_484_, 1, v___x_480_);
        leanh::lean_ctor_set(v___x_484_, 2, v___x_482_);
        leanh::lean_ctor_set(v___x_484_, 3, v___x_483_);
        v___x_485_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__14;
        v___x_486_ = l_Lean_Syntax_node2(v___x_463_, v___x_485_, v___x_459_, v___x_461_);
        v___x_487_ = l_Lean_Syntax_node2(v___x_463_, v___x_479_, v___x_484_, v___x_486_);
        v___x_488_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__17;
        v___x_489_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_489_, 0, v___x_463_);
        leanh::lean_ctor_set(v___x_489_, 1, v___x_488_);
        v___x_490_ =
            l_Lean_Syntax_node3(v___x_463_, v___x_467_, v___x_478_, v___x_487_, v___x_489_);
        v___x_491_ = l_Lean_Syntax_node2(v___x_463_, v___x_464_, v___x_466_, v___x_490_);
        v___x_492_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_492_, 0, v___x_491_);
        leanh::lean_ctor_set(v___x_492_, 1, v_a_450_);
        return v___x_492_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___boxed(
    mut v_x_493_: *mut leanh::LeanObject,
    mut v_a_494_: *mut leanh::LeanObject,
    mut v_a_495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_496_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1(v_x_493_, v_a_494_, v_a_495_);
    leanh::lean_dec_ref(v_a_494_);
    return v_res_496_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_PropLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_PropLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(builtin);
}