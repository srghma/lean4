// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Entails
// Imports: Init.PropLemmas
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5,
    l_Lean_Name_mkStr6, l_Lean_Name_mkStr7, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_addMacroScope, l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::PropLemmas::{
    initialize_Init_PropLemmas, runtime_initialize_Init_PropLemmas,
};
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__0_value:
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
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__1_value:
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
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__2_value:
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
    m_data: [66, 86, 68, 101, 99, 105, 100, 101, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__3_value:
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
    m_data: [76, 82, 65, 84, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__4_value:
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
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__5_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_1:
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
            l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__1_value)
            as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_2:
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
            l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__2_value)
            as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_3:
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
            l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        14108742078913166941 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_4:
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
            l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__4_value)
            as *mut crate::leanh::LeanObject,
        16855598961848779312 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value:
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
            l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value_aux_4
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__5_value)
            as *mut crate::leanh::LeanObject,
        9107789374283114430 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__7_value:
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
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__8_value:
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
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__7_value)
            as *mut crate::leanh::LeanObject,
        12571085391447129896 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__9_value:
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
    m_data: [32, 226, 138, 168, 32, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__10_value:
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
        l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__9_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__11_value:
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
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__12_value:
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
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__11_value)
            as *mut crate::leanh::LeanObject,
        8609355255726335675 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__13_value:
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
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__12_value)
            as *mut crate::leanh::LeanObject,
        (((26 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__14_value:
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
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__10_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__15_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6_value)
            as *mut crate::leanh::LeanObject,
        (((25 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((26 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__14_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__3_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__5_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [69, 110, 116, 97, 105, 108, 115, 46, 101, 118, 97, 108, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__7_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [69, 110, 116, 97, 105, 108, 115, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__8_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [101, 118, 97, 108, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__8_value) as *mut crate::leanh::LeanObject;
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__7_value) as *mut crate::leanh::LeanObject,6742649520003532491 as *mut crate::leanh::LeanObject] };
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__8_value) as *mut crate::leanh::LeanObject,899181493805419292 as *mut crate::leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__9_value) as *mut crate::leanh::LeanObject;
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__3_value) as *mut crate::leanh::LeanObject,14108742078913166941 as *mut crate::leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__4_value) as *mut crate::leanh::LeanObject,16855598961848779312 as *mut crate::leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_5: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__7_value) as *mut crate::leanh::LeanObject,9209341331324411620 as *mut crate::leanh::LeanObject] };
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value_aux_5) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__8_value) as *mut crate::leanh::LeanObject,7561698742759983679 as *mut crate::leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__12_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__11_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__13_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__13_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__0_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__0_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_1:
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
            l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__1_value)
            as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_2:
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
            l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__2_value)
            as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_3:
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
            l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        14108742078913166941 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_4:
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
            l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__4_value)
            as *mut crate::leanh::LeanObject,
        16855598961848779312 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value:
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
            l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value_aux_4
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        3721930517597245316 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__2_value:
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
    m_data: [32, 226, 138, 173, 32, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__3_value:
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
        l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__4_value:
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
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__12_value)
            as *mut crate::leanh::LeanObject,
        (((30 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__5_value:
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
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__6_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((25 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((25 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 6, m_data: [116, 101, 114, 109, 194, 172, 95, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__0_value) as *mut crate::leanh::LeanObject,17055224711078181598 as *mut crate::leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__2_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 1, m_data: [194, 172, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__3_value) as *mut crate::leanh::LeanObject,7932075773091973500 as *mut crate::leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__5_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__5_value) as *mut crate::leanh::LeanObject;
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__5_value) as *mut crate::leanh::LeanObject,7306243862518720553 as *mut crate::leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__7_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__8_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__8_value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__10_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__3_value) as *mut crate::leanh::LeanObject,14108742078913166941 as *mut crate::leanh::LeanObject] };
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__4_value) as *mut crate::leanh::LeanObject,16855598961848779312 as *mut crate::leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__13_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__12_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__14_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__13_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__15_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__16_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__15_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__17_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__17_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_294_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__5;
    v___x_295_ = l_String_toRawSubstring_x27(v___x_294_);
    return v___x_295_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1(
    mut v_x_318_: *mut crate::leanh::LeanObject,
    mut v_a_319_: *mut crate::leanh::LeanObject,
    mut v_a_320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: u8 = 0;
    v___x_321_ = l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6;
    crate::leanh::lean_inc(v_x_318_);
    v___x_322_ = l_Lean_Syntax_isOfKind(v_x_318_, v___x_321_);
    if v___x_322_ == 0 {
        let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_318_);
        v___x_323_ = crate::leanh::lean_box(1);
        v___x_324_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_324_, 0, v___x_323_);
        crate::leanh::lean_ctor_set(v___x_324_, 1, v_a_320_);
        return v___x_324_;
    } else {
        let mut v_quotContext_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_332_: u8 = 0;
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
        v_quotContext_325_ = crate::leanh::lean_ctor_get(v_a_319_, 1);
        v_currMacroScope_326_ = crate::leanh::lean_ctor_get(v_a_319_, 2);
        v_ref_327_ = crate::leanh::lean_ctor_get(v_a_319_, 5);
        v___x_328_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_329_ = l_Lean_Syntax_getArg(v_x_318_, v___x_328_);
        v___x_330_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_331_ = l_Lean_Syntax_getArg(v_x_318_, v___x_330_);
        crate::leanh::lean_dec(v_x_318_);
        v___x_332_ = 0;
        v___x_333_ = l_Lean_SourceInfo_fromRef(v_ref_327_, v___x_332_);
        v___x_334_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4;
        v___x_335_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6_once), _init_l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6);
        v___x_336_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__9;
        crate::leanh::lean_inc(v_currMacroScope_326_);
        crate::leanh::lean_inc(v_quotContext_325_);
        v___x_337_ = l_Lean_addMacroScope(v_quotContext_325_, v___x_336_, v_currMacroScope_326_);
        v___x_338_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__12;
        crate::leanh::lean_inc_n(v___x_333_, 2);
        v___x_339_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_339_, 0, v___x_333_);
        crate::leanh::lean_ctor_set(v___x_339_, 1, v___x_335_);
        crate::leanh::lean_ctor_set(v___x_339_, 2, v___x_337_);
        crate::leanh::lean_ctor_set(v___x_339_, 3, v___x_338_);
        v___x_340_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__14;
        v___x_341_ = l_Lean_Syntax_node2(v___x_333_, v___x_340_, v___x_329_, v___x_331_);
        v___x_342_ = l_Lean_Syntax_node2(v___x_333_, v___x_334_, v___x_339_, v___x_341_);
        v___x_343_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_343_, 0, v___x_342_);
        crate::leanh::lean_ctor_set(v___x_343_, 1, v_a_320_);
        return v___x_343_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___boxed(
    mut v_x_344_: *mut crate::leanh::LeanObject,
    mut v_a_345_: *mut crate::leanh::LeanObject,
    mut v_a_346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_347_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1(v_x_344_, v_a_345_, v_a_346_);
    crate::leanh::lean_dec_ref(v_a_345_);
    return v_res_347_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1(
    mut v_x_351_: *mut crate::leanh::LeanObject,
    mut v_a_352_: *mut crate::leanh::LeanObject,
    mut v_a_353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: u8 = 0;
    v___x_354_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4;
    crate::leanh::lean_inc(v_x_351_);
    v___x_355_ = l_Lean_Syntax_isOfKind(v_x_351_, v___x_354_);
    if v___x_355_ == 0 {
        let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_351_);
        v___x_356_ = crate::leanh::lean_box(0);
        v___x_357_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_357_, 0, v___x_356_);
        crate::leanh::lean_ctor_set(v___x_357_, 1, v_a_353_);
        return v___x_357_;
    } else {
        let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_361_: u8 = 0;
        v___x_358_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_359_ = l_Lean_Syntax_getArg(v_x_351_, v___x_358_);
        v___x_360_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___closed__1;
        crate::leanh::lean_inc(v___x_359_);
        v___x_361_ = l_Lean_Syntax_isOfKind(v___x_359_, v___x_360_);
        if v___x_361_ == 0 {
            let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_359_);
            crate::leanh::lean_dec(v_x_351_);
            v___x_362_ = crate::leanh::lean_box(0);
            v___x_363_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_363_, 0, v___x_362_);
            crate::leanh::lean_ctor_set(v___x_363_, 1, v_a_353_);
            return v___x_363_;
        } else {
            let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_367_: u8 = 0;
            v___x_364_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_365_ = l_Lean_Syntax_getArg(v_x_351_, v___x_364_);
            crate::leanh::lean_dec(v_x_351_);
            v___x_366_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_365_);
            v___x_367_ = l_Lean_Syntax_matchesNull(v___x_365_, v___x_366_);
            if v___x_367_ == 0 {
                let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_365_);
                crate::leanh::lean_dec(v___x_359_);
                v___x_368_ = crate::leanh::lean_box(0);
                v___x_369_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_369_, 0, v___x_368_);
                crate::leanh::lean_ctor_set(v___x_369_, 1, v_a_353_);
                return v___x_369_;
            } else {
                let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_373_: u8 = 0;
                let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_370_ = l_Lean_Syntax_getArg(v___x_365_, v___x_358_);
                v___x_371_ = l_Lean_Syntax_getArg(v___x_365_, v___x_364_);
                crate::leanh::lean_dec(v___x_365_);
                v_ref_372_ = l_Lean_replaceRef(v___x_359_, v_a_352_);
                crate::leanh::lean_dec(v___x_359_);
                v___x_373_ = 0;
                v___x_374_ = l_Lean_SourceInfo_fromRef(v_ref_372_, v___x_373_);
                crate::leanh::lean_dec(v_ref_372_);
                v___x_375_ = l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__6;
                v___x_376_ = l_Std_Tactic_BVDecide_LRAT_Internal_term___u22a8___00__closed__9;
                crate::leanh::lean_inc(v___x_374_);
                v___x_377_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_377_, 0, v___x_374_);
                crate::leanh::lean_ctor_set(v___x_377_, 1, v___x_376_);
                v___x_378_ =
                    l_Lean_Syntax_node3(v___x_374_, v___x_375_, v___x_370_, v___x_377_, v___x_371_);
                v___x_379_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_379_, 0, v___x_378_);
                crate::leanh::lean_ctor_set(v___x_379_, 1, v_a_353_);
                return v___x_379_;
            }
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1___boxed(
    mut v_x_380_: *mut crate::leanh::LeanObject,
    mut v_a_381_: *mut crate::leanh::LeanObject,
    mut v_a_382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_383_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______unexpand__Std__Tactic__BVDecide__LRAT__Internal__Entails__eval__1(v_x_380_, v_a_381_, v_a_382_);
    crate::leanh::lean_dec(v_a_381_);
    return v_res_383_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_428_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__10;
    v___x_429_ = l_String_toRawSubstring_x27(v___x_428_);
    return v___x_429_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1(
    mut v_x_448_: *mut crate::leanh::LeanObject,
    mut v_a_449_: *mut crate::leanh::LeanObject,
    mut v_a_450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: u8 = 0;
    v___x_451_ = l_Std_Tactic_BVDecide_LRAT_Internal_term___u22ad___00__closed__1;
    crate::leanh::lean_inc(v_x_448_);
    v___x_452_ = l_Lean_Syntax_isOfKind(v_x_448_, v___x_451_);
    if v___x_452_ == 0 {
        let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_448_);
        v___x_453_ = crate::leanh::lean_box(1);
        v___x_454_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_454_, 0, v___x_453_);
        crate::leanh::lean_ctor_set(v___x_454_, 1, v_a_450_);
        return v___x_454_;
    } else {
        let mut v_quotContext_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_462_: u8 = 0;
        let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_455_ = crate::leanh::lean_ctor_get(v_a_449_, 1);
        v_currMacroScope_456_ = crate::leanh::lean_ctor_get(v_a_449_, 2);
        v_ref_457_ = crate::leanh::lean_ctor_get(v_a_449_, 5);
        v___x_458_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_459_ = l_Lean_Syntax_getArg(v_x_448_, v___x_458_);
        v___x_460_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_461_ = l_Lean_Syntax_getArg(v_x_448_, v___x_460_);
        crate::leanh::lean_dec(v_x_448_);
        v___x_462_ = 0;
        v___x_463_ = l_Lean_SourceInfo_fromRef(v_ref_457_, v___x_462_);
        v___x_464_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__1;
        v___x_465_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__2;
        crate::leanh::lean_inc_n(v___x_463_, 10);
        v___x_466_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_466_, 0, v___x_463_);
        crate::leanh::lean_ctor_set(v___x_466_, 1, v___x_465_);
        v___x_467_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__4;
        v___x_468_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__6;
        v___x_469_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__7;
        v___x_470_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_470_, 0, v___x_463_);
        crate::leanh::lean_ctor_set(v___x_470_, 1, v___x_469_);
        v___x_471_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__9;
        v___x_472_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__11), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__11_once), _init_l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__11);
        v___x_473_ = crate::leanh::lean_box(0);
        crate::leanh::lean_inc_n(v_currMacroScope_456_, 2);
        crate::leanh::lean_inc_n(v_quotContext_455_, 2);
        v___x_474_ = l_Lean_addMacroScope(v_quotContext_455_, v___x_473_, v_currMacroScope_456_);
        v___x_475_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__14;
        v___x_476_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_476_, 0, v___x_463_);
        crate::leanh::lean_ctor_set(v___x_476_, 1, v___x_472_);
        crate::leanh::lean_ctor_set(v___x_476_, 2, v___x_474_);
        crate::leanh::lean_ctor_set(v___x_476_, 3, v___x_475_);
        v___x_477_ = l_Lean_Syntax_node1(v___x_463_, v___x_471_, v___x_476_);
        v___x_478_ = l_Lean_Syntax_node2(v___x_463_, v___x_468_, v___x_470_, v___x_477_);
        v___x_479_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__4;
        v___x_480_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6_once), _init_l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__6);
        v___x_481_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__9;
        v___x_482_ = l_Lean_addMacroScope(v_quotContext_455_, v___x_481_, v_currMacroScope_456_);
        v___x_483_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__16;
        v___x_484_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_484_, 0, v___x_463_);
        crate::leanh::lean_ctor_set(v___x_484_, 1, v___x_480_);
        crate::leanh::lean_ctor_set(v___x_484_, 2, v___x_482_);
        crate::leanh::lean_ctor_set(v___x_484_, 3, v___x_483_);
        v___x_485_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22a8____1___closed__14;
        v___x_486_ = l_Lean_Syntax_node2(v___x_463_, v___x_485_, v___x_459_, v___x_461_);
        v___x_487_ = l_Lean_Syntax_node2(v___x_463_, v___x_479_, v___x_484_, v___x_486_);
        v___x_488_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___closed__17;
        v___x_489_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_489_, 0, v___x_463_);
        crate::leanh::lean_ctor_set(v___x_489_, 1, v___x_488_);
        v___x_490_ =
            l_Lean_Syntax_node3(v___x_463_, v___x_467_, v___x_478_, v___x_487_, v___x_489_);
        v___x_491_ = l_Lean_Syntax_node2(v___x_463_, v___x_464_, v___x_466_, v___x_490_);
        v___x_492_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_492_, 0, v___x_491_);
        crate::leanh::lean_ctor_set(v___x_492_, 1, v_a_450_);
        return v___x_492_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1___boxed(
    mut v_x_493_: *mut crate::leanh::LeanObject,
    mut v_a_494_: *mut crate::leanh::LeanObject,
    mut v_a_495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_496_ = l_Std_Tactic_BVDecide_LRAT_Internal___aux__Std__Tactic__BVDecide__LRAT__Internal__Entails______macroRules__Std__Tactic__BVDecide__LRAT__Internal__term___u22ad____1(v_x_493_, v_a_494_, v_a_495_);
    crate::leanh::lean_dec_ref(v_a_494_);
    return v_res_496_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_PropLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_PropLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_Entails(builtin);
}
