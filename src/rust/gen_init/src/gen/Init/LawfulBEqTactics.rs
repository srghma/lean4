// Lean compiler output
// Module: Init.LawfulBEqTactics
// Imports: Init.Core Init.Data.Bool Init.ByCases Init.Classical
use crate::ffi::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Classical::{initialize_Init_Classical, runtime_initialize_Init_Classical};
use crate::r#gen::Init::Core::{initialize_Init_Core, runtime_initialize_Init_Core};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_node5,
    l_Lean_Syntax_node6, l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
pub static l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__0_value:
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
        68, 101, 114, 105, 118, 105, 110, 103, 72, 101, 108, 112, 101, 114, 115, 0,
    ],
};
static mut l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__1_value:
    leanh::LeanStringObject<29> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        116, 97, 99, 116, 105, 99, 68, 101, 114, 105, 118, 105, 110, 103, 95, 82, 101, 102, 108,
        69, 113, 95, 116, 97, 99, 116, 105, 99, 0,
    ],
};
static mut l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__1_value)
        as *mut leanh::LeanObject;
static l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__0_value)
            as *mut leanh::LeanObject,
        15296920709769342228 as *mut leanh::LeanObject,
    ],
};
pub static l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__2_value:
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
            l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__2_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__1_value)
            as *mut leanh::LeanObject,
        8670410953647023675 as *mut leanh::LeanObject,
    ],
};
static mut l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__3_value:
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
        100, 101, 114, 105, 118, 105, 110, 103, 95, 82, 101, 102, 108, 69, 113, 95, 116, 97, 99,
        116, 105, 99, 0,
    ],
};
static mut l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__4_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__3_value)
            as *mut leanh::LeanObject,
        0 as *mut leanh::LeanObject,
    ],
};
static mut l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__5_value:
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
        core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__2_value)
            as *mut leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_DerivingHelpers_tacticDeriving__ReflEq__tactic: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__3_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__3_value) as *mut leanh::LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__3_value) as *mut leanh::LeanObject,8689124066155232629 as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__6_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__6_value) as *mut leanh::LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__6_value) as *mut leanh::LeanObject,8504843326314613972 as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__8_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__8_value) as *mut leanh::LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__8_value) as *mut leanh::LeanObject,17228437386856258271 as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__10_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__10_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__10_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 110, 116, 114, 111, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12_value) as *mut leanh::LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12_value) as *mut leanh::LeanObject,5665407707378192681 as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__14_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__14_value) as *mut leanh::LeanObject;
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__16_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__14_value) as *mut leanh::LeanObject,13655884332201764339 as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__16_value) as *mut leanh::LeanObject;
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__18_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__18_value) as *mut leanh::LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__18_value) as *mut leanh::LeanObject,1203031414467445991 as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__20_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 108, 105, 109, 84, 97, 114, 103, 101, 116, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__20_value) as *mut leanh::LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__20_value) as *mut leanh::LeanObject,12379583263280086920 as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__22_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 108, 108, 71, 111, 97, 108, 115, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__22_value) as *mut leanh::LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__22_value) as *mut leanh::LeanObject,14131640301685195369 as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__24_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 108, 108, 95, 103, 111, 97, 108, 115, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__24_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25_value) as *mut leanh::LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25_value) as *mut leanh::LeanObject,12783917532758215986 as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__27_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__27_value) as *mut leanh::LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__27_value) as *mut leanh::LeanObject,3488656302031949961 as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__29_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [111, 110, 108, 121, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__29_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__30_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__30_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__31_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 105, 109, 112, 76, 101, 109, 109, 97, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__31_value) as *mut leanh::LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__31_value) as *mut leanh::LeanObject,7383208167966365478 as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__33_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [66, 69, 113, 46, 114, 101, 102, 108, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__33: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__33_value) as *mut leanh::LeanObject;
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__34_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__34: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__35_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [66, 69, 113, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__35: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__35_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__36_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [114, 101, 102, 108, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__36: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__36_value) as *mut leanh::LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__37_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__35_value) as *mut leanh::LeanObject,16093780639914376387 as *mut leanh::LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__37_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__37_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__36_value) as *mut leanh::LeanObject,2931058100974671924 as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__37: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__37_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__38_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__37_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__38: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__38_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__39_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__38_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__39: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__39_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__40_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__40: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__40_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__41_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [115, 105, 109, 112, 80, 114, 101, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__41: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__41_value) as *mut leanh::LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__41_value) as *mut leanh::LeanObject,10994783280459430853 as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__43_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 134, 147, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__43: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__43_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__44_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 100, 117, 99, 101, 68, 73, 116, 101, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__44: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__44_value) as *mut leanh::LeanObject;
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__45_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__45: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__46_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__44_value) as *mut leanh::LeanObject,5427593982451803422 as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__46: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__46_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__47_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [66, 111, 111, 108, 46, 97, 110, 100, 95, 116, 114, 117, 101, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__47: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__47_value) as *mut leanh::LeanObject;
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__48_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__48: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__49_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__49: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__49_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__50_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 110, 100, 95, 116, 114, 117, 101, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__50: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__50_value) as *mut leanh::LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__51_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__49_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__51_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__51_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__50_value) as *mut leanh::LeanObject,4834393437129725208 as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__51: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__51_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__52_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__51_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__52: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__52_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__53_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__52_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__53: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__53_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__54_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 105, 109, 112, 83, 116, 97, 114, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__54: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__54_value) as *mut leanh::LeanObject;
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__54_value) as *mut leanh::LeanObject,2669418402702632573 as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__56_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [42, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__56: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__56_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__57_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 101, 100, 117, 99, 101, 66, 69, 113, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__57: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__57_value) as *mut leanh::LeanObject;
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__59_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__57_value) as *mut leanh::LeanObject,7878093518326082311 as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__59: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__59_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__60_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [114, 101, 100, 117, 99, 101, 67, 116, 111, 114, 73, 100, 120, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__60: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__60_value) as *mut leanh::LeanObject;
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__62_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__60_value) as *mut leanh::LeanObject,11681431521506135087 as *mut leanh::LeanObject] };
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__62: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__62_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__63_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__63: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__63_value) as *mut leanh::LeanObject;
pub static l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64: *mut leanh::LeanObject = core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64_value) as *mut leanh::LeanObject;
pub static l_tacticDeriving__LawfulEq__tactic__step___closed__0_value:
    leanh::LeanStringObject<36> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        116, 97, 99, 116, 105, 99, 68, 101, 114, 105, 118, 105, 110, 103, 95, 76, 97, 119, 102,
        117, 108, 69, 113, 95, 116, 97, 99, 116, 105, 99, 95, 115, 116, 101, 112, 0,
    ],
};
static mut l_tacticDeriving__LawfulEq__tactic__step___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic__step___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_tacticDeriving__LawfulEq__tactic__step___closed__1_value:
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
        core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic__step___closed__0_value)
            as *mut leanh::LeanObject,
        5824473086672787675 as *mut leanh::LeanObject,
    ],
};
static mut l_tacticDeriving__LawfulEq__tactic__step___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic__step___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_tacticDeriving__LawfulEq__tactic__step___closed__2_value:
    leanh::LeanStringObject<30> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        100, 101, 114, 105, 118, 105, 110, 103, 95, 76, 97, 119, 102, 117, 108, 69, 113, 95, 116,
        97, 99, 116, 105, 99, 95, 115, 116, 101, 112, 0,
    ],
};
static mut l_tacticDeriving__LawfulEq__tactic__step___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic__step___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_tacticDeriving__LawfulEq__tactic__step___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic__step___closed__2_value)
            as *mut leanh::LeanObject,
        0 as *mut leanh::LeanObject,
    ],
};
static mut l_tacticDeriving__LawfulEq__tactic__step___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic__step___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_tacticDeriving__LawfulEq__tactic__step___closed__4_value:
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
        core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic__step___closed__1_value)
            as *mut leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic__step___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_tacticDeriving__LawfulEq__tactic__step___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic__step___closed__4_value)
        as *mut leanh::LeanObject;
pub static mut l_tacticDeriving__LawfulEq__tactic__step: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic__step___closed__4_value)
        as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [102, 97, 105, 108, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__0_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__0_value) as *mut leanh::LeanObject,59994724629665531 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [115, 116, 114, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__2_value) as *mut leanh::LeanObject,9232979286016572671 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__4_value: leanh::LeanStringObject<39> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [34, 100, 101, 114, 105, 118, 105, 110, 103, 95, 76, 97, 119, 102, 117, 108, 69, 113, 95, 116, 97, 99, 116, 105, 99, 95, 115, 116, 101, 112, 32, 102, 97, 105, 108, 101, 100, 34, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__0_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [119, 105, 116, 104, 82, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__0_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__0_value) as *mut leanh::LeanObject,6022092293134036165 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__2_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [119, 105, 116, 104, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__2_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__3_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 104, 97, 110, 103, 101, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__3_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__3_value) as *mut leanh::LeanObject,16580879115603664356 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__6_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 114, 114, 111, 119, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__6_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__6_value) as *mut leanh::LeanObject,14917456309791986358 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__8_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 95, 61, 95, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__8_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__8_value) as *mut leanh::LeanObject,5677895497334651815 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__9_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__10_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__10_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__10_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__12_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 105, 116, 101, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__12_value) as *mut leanh::LeanObject;
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__12_value) as *mut leanh::LeanObject,8391571994004792969 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__14_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__15_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__14_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__15_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__16_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__15_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__16_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__3_value) as *mut leanh::LeanObject,7932075773091973500 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__18_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__18_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__18_value) as *mut leanh::LeanObject,7306243862518720553 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__20_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__20_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__21_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__20_value) as *mut leanh::LeanObject,9871775667037945883 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__21_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__22_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__22_value) as *mut leanh::LeanObject;
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__24_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__24_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__25_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__24_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__25_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__26_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 101, 114, 109, 95, 61, 61, 95, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__26_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__27_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__26_value) as *mut leanh::LeanObject,1990087968466729753 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__27_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__28_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__28_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__28_value) as *mut leanh::LeanObject,3984140175429830279 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__30_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__30_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__31_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 61, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__31_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__32_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [61, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__32_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__33_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__33: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__33_value) as *mut leanh::LeanObject;
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__35_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__33_value) as *mut leanh::LeanObject,6560861498103128555 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__35: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__35_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__36_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__49_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__36_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__36_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__33_value) as *mut leanh::LeanObject,9255189395584251158 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__36: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__36_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__37_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__36_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__37: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__37_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__38_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__37_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__38: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__38_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__39_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 134, 146, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__39: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__39_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__40_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 101, 102, 105, 110, 101, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__40: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__40_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__40_value) as *mut leanh::LeanObject,17704266427038597681 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__42_value: leanh::LeanStringObject<47> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [68, 101, 114, 105, 118, 105, 110, 103, 72, 101, 108, 112, 101, 114, 115, 46, 100, 101, 114, 105, 118, 105, 110, 103, 95, 108, 97, 119, 102, 117, 108, 95, 98, 101, 113, 95, 104, 101, 108, 112, 101, 114, 95, 100, 101, 112, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__42: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__42_value) as *mut leanh::LeanObject;
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__43_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__43: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__44_value: leanh::LeanStringObject<31> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [100, 101, 114, 105, 118, 105, 110, 103, 95, 108, 97, 119, 102, 117, 108, 95, 98, 101, 113, 95, 104, 101, 108, 112, 101, 114, 95, 100, 101, 112, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__44: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__44_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__45_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__0_value) as *mut leanh::LeanObject,15296920709769342228 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__45_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__45_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__44_value) as *mut leanh::LeanObject,8566119949188782736 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__45: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__45_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__46_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__45_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__46: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__46_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__47_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__46_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__47: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__47_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__48_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 121, 110, 116, 104, 101, 116, 105, 99, 72, 111, 108, 101, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__48: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__48_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__5_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__48_value) as *mut leanh::LeanObject,11921244625177918938 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__50_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [63, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__50: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__50_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__51_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 100, 111, 116, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__51: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__51_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__52_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__52_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__52_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__51_value) as *mut leanh::LeanObject,17509453262750390254 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__52: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__52_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__53_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 100, 111, 116, 84, 107, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__53: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__53_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__54_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__54_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__54_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__53_value) as *mut leanh::LeanObject,10467776374279798389 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__54: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__54_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__55_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 1, m_data: [194, 183, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__55: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__55_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__56_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [115, 111, 108, 118, 101, 84, 97, 99, 116, 105, 99, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__56: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__56_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__57_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__57_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__57_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__56_value) as *mut leanh::LeanObject,17642938439725768139 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__57: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__57_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__58_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 111, 108, 118, 101, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__58: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__58_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__59_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 111, 117, 112, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__59: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__59_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__60_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__59_value) as *mut leanh::LeanObject,2214559063752339918 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__60: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__60_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__61_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__61: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__61_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__62_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [97, 112, 112, 108, 121, 65, 115, 115, 117, 109, 112, 116, 105, 111, 110, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__62: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__62_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__62_value) as *mut leanh::LeanObject,6767535199982504454 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__64_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [97, 112, 112, 108, 121, 95, 97, 115, 115, 117, 109, 112, 116, 105, 111, 110, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__64: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__64_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__65_value: leanh::LeanStringObject<43> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [34, 99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 105, 115, 99, 104, 97, 114, 103, 101, 32, 101, 113, 95, 111, 102, 95, 98, 101, 113, 32, 97, 115, 115, 117, 109, 112, 116, 105, 111, 110, 34, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__65: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__65_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__66_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__66: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__66_value) as *mut leanh::LeanObject;
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__68_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__66_value) as *mut leanh::LeanObject,8738205681931236784 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__68: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__68_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__69_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 97, 115, 101, 115, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__69: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__69_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__69_value) as *mut leanh::LeanObject,5378309054007488965 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__71_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 115, 105, 109, 112, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__71: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__71_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__71_value) as *mut leanh::LeanObject,5511199417188169206 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__24_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__36_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__2_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__1_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__3_value: leanh::LeanStringObject<46> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [68, 101, 114, 105, 118, 105, 110, 103, 72, 101, 108, 112, 101, 114, 115, 46, 100, 101, 114, 105, 118, 105, 110, 103, 95, 108, 97, 119, 102, 117, 108, 95, 98, 101, 113, 95, 104, 101, 108, 112, 101, 114, 95, 110, 100, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__3_value) as *mut leanh::LeanObject;
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__5_value: leanh::LeanStringObject<30> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [100, 101, 114, 105, 118, 105, 110, 103, 95, 108, 97, 119, 102, 117, 108, 95, 98, 101, 113, 95, 104, 101, 108, 112, 101, 114, 95, 110, 100, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__5_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__0_value) as *mut leanh::LeanObject,15296920709769342228 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__5_value) as *mut leanh::LeanObject,14609763185561287494 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__6_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__7_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__6_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__7_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__8_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__7_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__8_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__9_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 117, 98, 115, 116, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__9_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__9_value) as *mut leanh::LeanObject,10450510229121596744 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 101, 114, 109, 95, 38, 38, 95, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__0_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__0_value) as *mut leanh::LeanObject,1601449343645893382 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__1_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__2_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [38, 38, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__2_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__3_value: leanh::LeanStringObject<31> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [68, 101, 114, 105, 118, 105, 110, 103, 72, 101, 108, 112, 101, 114, 115, 46, 97, 110, 100, 95, 116, 114, 117, 101, 95, 99, 117, 114, 114, 121, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__3_value) as *mut leanh::LeanObject;
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__5_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [97, 110, 100, 95, 116, 114, 117, 101, 95, 99, 117, 114, 114, 121, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__5_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__0_value) as *mut leanh::LeanObject,15296920709769342228 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__5_value) as *mut leanh::LeanObject,17404699193326600018 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__6_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__7_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__6_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__7_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__8_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__7_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__8_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 82, 102, 108, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__0_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__0_value) as *mut leanh::LeanObject,3294379458557754569 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [114, 102, 108, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__2_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 101, 113, 49, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__0_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__0_value) as *mut leanh::LeanObject,8471002125274025202 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__2_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__3_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [116, 97, 99, 116, 105, 99, 84, 114, 105, 118, 105, 97, 108, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__3_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__3_value) as *mut leanh::LeanObject,2766452847008772443 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__5_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 114, 105, 118, 105, 97, 108, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__5_value) as *mut leanh::LeanObject;
pub static l_tacticDeriving__LawfulEq__tactic___closed__0_value: leanh::LeanStringObject<
    31,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        116, 97, 99, 116, 105, 99, 68, 101, 114, 105, 118, 105, 110, 103, 95, 76, 97, 119, 102,
        117, 108, 69, 113, 95, 116, 97, 99, 116, 105, 99, 0,
    ],
};
static mut l_tacticDeriving__LawfulEq__tactic___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_tacticDeriving__LawfulEq__tactic___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic___closed__0_value)
                as *mut leanh::LeanObject,
            12369115935240678623 as *mut leanh::LeanObject,
        ],
    };
static mut l_tacticDeriving__LawfulEq__tactic___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_tacticDeriving__LawfulEq__tactic___closed__2_value: leanh::LeanStringObject<
    25,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        100, 101, 114, 105, 118, 105, 110, 103, 95, 76, 97, 119, 102, 117, 108, 69, 113, 95, 116,
        97, 99, 116, 105, 99, 0,
    ],
};
static mut l_tacticDeriving__LawfulEq__tactic___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_tacticDeriving__LawfulEq__tactic___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic___closed__2_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_tacticDeriving__LawfulEq__tactic___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_tacticDeriving__LawfulEq__tactic___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic___closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_tacticDeriving__LawfulEq__tactic___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic___closed__4_value)
        as *mut leanh::LeanObject;
pub static mut l_tacticDeriving__LawfulEq__tactic: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_tacticDeriving__LawfulEq__tactic___closed__4_value)
        as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [121, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__0_value) as *mut leanh::LeanObject;
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,10873459229016405832 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__3_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [116, 97, 99, 116, 105, 99, 82, 101, 112, 101, 97, 116, 95, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__3_value) as *mut leanh::LeanObject;
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__3_value) as *mut leanh::LeanObject,16592576665728214421 as *mut leanh::LeanObject] };
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__5_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 101, 112, 101, 97, 116, 0]};
static mut l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__5_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1216_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__14;
    v___x_1217_ = l_String_toRawSubstring_x27(v___x_1216_);
    return v___x_1217_;
}
pub unsafe fn _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1220_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_1220_;
}
pub unsafe fn _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__34()
-> *mut leanh::LeanObject {
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1261_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__33;
    v___x_1262_ = l_String_toRawSubstring_x27(v___x_1261_);
    return v___x_1262_;
}
pub unsafe fn _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__45()
-> *mut leanh::LeanObject {
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1283_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__44;
    v___x_1284_ = l_String_toRawSubstring_x27(v___x_1283_);
    return v___x_1284_;
}
pub unsafe fn _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__48()
-> *mut leanh::LeanObject {
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1288_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__47;
    v___x_1289_ = l_String_toRawSubstring_x27(v___x_1288_);
    return v___x_1289_;
}
pub unsafe fn _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58()
-> *mut leanh::LeanObject {
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1309_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__57;
    v___x_1310_ = l_String_toRawSubstring_x27(v___x_1309_);
    return v___x_1310_;
}
pub unsafe fn _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61()
-> *mut leanh::LeanObject {
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1314_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__60;
    v___x_1315_ = l_String_toRawSubstring_x27(v___x_1314_);
    return v___x_1315_;
}
pub unsafe fn l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1(
    mut v_x_1320_: *mut leanh::LeanObject,
    mut v_a_1321_: *mut leanh::LeanObject,
    mut v_a_1322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: u8 = 0;
    v___x_1323_ = l_DerivingHelpers_tacticDeriving__ReflEq__tactic___closed__2;
    v___x_1324_ = l_Lean_Syntax_isOfKind(v_x_1320_, v___x_1323_);
    if v___x_1324_ == 0 {
        let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1325_ = leanh::lean_box(1);
        v___x_1326_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1326_, 0, v___x_1325_);
        leanh::lean_ctor_set(v___x_1326_, 1, v_a_1322_);
        return v___x_1326_;
    } else {
        let mut v_quotContext_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1330_: u8 = 0;
        let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
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
        let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
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
        let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1327_ = leanh::lean_ctor_get(v_a_1321_, 1);
        v_currMacroScope_1328_ = leanh::lean_ctor_get(v_a_1321_, 2);
        v_ref_1329_ = leanh::lean_ctor_get(v_a_1321_, 5);
        v___x_1330_ = 0;
        v___x_1331_ = l_Lean_SourceInfo_fromRef(v_ref_1329_, v___x_1330_);
        v___x_1332_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4;
        v___x_1333_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5;
        leanh::lean_inc_n(v___x_1331_, 44);
        v___x_1334_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1334_, 0, v___x_1331_);
        leanh::lean_ctor_set(v___x_1334_, 1, v___x_1333_);
        v___x_1335_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7;
        v___x_1336_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9;
        v___x_1337_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11;
        v___x_1338_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12;
        v___x_1339_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13;
        v___x_1340_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1340_, 0, v___x_1331_);
        leanh::lean_ctor_set(v___x_1340_, 1, v___x_1338_);
        v___x_1341_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15);
        v___x_1342_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__16;
        leanh::lean_inc_n(v_currMacroScope_1328_, 6);
        leanh::lean_inc_n(v_quotContext_1327_, 6);
        v___x_1343_ =
            l_Lean_addMacroScope(v_quotContext_1327_, v___x_1342_, v_currMacroScope_1328_);
        v___x_1344_ = leanh::lean_box(0);
        v___x_1345_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1345_, 0, v___x_1331_);
        leanh::lean_ctor_set(v___x_1345_, 1, v___x_1341_);
        leanh::lean_ctor_set(v___x_1345_, 2, v___x_1343_);
        leanh::lean_ctor_set(v___x_1345_, 3, v___x_1344_);
        leanh::lean_inc_ref(v___x_1345_);
        v___x_1346_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1337_, v___x_1345_);
        v___x_1347_ = l_Lean_Syntax_node2(v___x_1331_, v___x_1339_, v___x_1340_, v___x_1346_);
        v___x_1348_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17);
        v___x_1349_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_1349_, 0, v___x_1331_);
        leanh::lean_ctor_set(v___x_1349_, 1, v___x_1337_);
        leanh::lean_ctor_set(v___x_1349_, 2, v___x_1348_);
        v___x_1350_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__18;
        v___x_1351_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19;
        v___x_1352_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1352_, 0, v___x_1331_);
        leanh::lean_ctor_set(v___x_1352_, 1, v___x_1350_);
        v___x_1353_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21;
        leanh::lean_inc_ref_n(v___x_1349_, 17);
        v___x_1354_ = l_Lean_Syntax_node2(v___x_1331_, v___x_1353_, v___x_1349_, v___x_1345_);
        v___x_1355_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1337_, v___x_1354_);
        v___x_1356_ = l_Lean_Syntax_node5(
            v___x_1331_,
            v___x_1351_,
            v___x_1352_,
            v___x_1355_,
            v___x_1349_,
            v___x_1349_,
            v___x_1349_,
        );
        v___x_1357_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23;
        v___x_1358_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__24;
        v___x_1359_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1359_, 0, v___x_1331_);
        leanh::lean_ctor_set(v___x_1359_, 1, v___x_1358_);
        v___x_1360_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25;
        v___x_1361_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26;
        v___x_1362_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1362_, 0, v___x_1331_);
        leanh::lean_ctor_set(v___x_1362_, 1, v___x_1360_);
        v___x_1363_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28;
        v___x_1364_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1363_, v___x_1349_);
        v___x_1365_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__29;
        v___x_1366_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1366_, 0, v___x_1331_);
        leanh::lean_ctor_set(v___x_1366_, 1, v___x_1365_);
        v___x_1367_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1337_, v___x_1366_);
        v___x_1368_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__30;
        v___x_1369_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1369_, 0, v___x_1331_);
        leanh::lean_ctor_set(v___x_1369_, 1, v___x_1368_);
        v___x_1370_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32;
        v___x_1371_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__34), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__34_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__34);
        v___x_1372_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__37;
        v___x_1373_ =
            l_Lean_addMacroScope(v_quotContext_1327_, v___x_1372_, v_currMacroScope_1328_);
        v___x_1374_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__39;
        v___x_1375_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1375_, 0, v___x_1331_);
        leanh::lean_ctor_set(v___x_1375_, 1, v___x_1371_);
        leanh::lean_ctor_set(v___x_1375_, 2, v___x_1373_);
        leanh::lean_ctor_set(v___x_1375_, 3, v___x_1374_);
        v___x_1376_ = l_Lean_Syntax_node3(
            v___x_1331_,
            v___x_1370_,
            v___x_1349_,
            v___x_1349_,
            v___x_1375_,
        );
        v___x_1377_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__40;
        v___x_1378_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1378_, 0, v___x_1331_);
        leanh::lean_ctor_set(v___x_1378_, 1, v___x_1377_);
        v___x_1379_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__42;
        v___x_1380_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__43;
        v___x_1381_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1381_, 0, v___x_1331_);
        leanh::lean_ctor_set(v___x_1381_, 1, v___x_1380_);
        v___x_1382_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1379_, v___x_1381_);
        v___x_1383_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1337_, v___x_1382_);
        v___x_1384_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__45), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__45_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__45);
        v___x_1385_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__46;
        v___x_1386_ =
            l_Lean_addMacroScope(v_quotContext_1327_, v___x_1385_, v_currMacroScope_1328_);
        v___x_1387_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1387_, 0, v___x_1331_);
        leanh::lean_ctor_set(v___x_1387_, 1, v___x_1384_);
        leanh::lean_ctor_set(v___x_1387_, 2, v___x_1386_);
        leanh::lean_ctor_set(v___x_1387_, 3, v___x_1344_);
        v___x_1388_ = l_Lean_Syntax_node3(
            v___x_1331_,
            v___x_1370_,
            v___x_1383_,
            v___x_1349_,
            v___x_1387_,
        );
        v___x_1389_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__48), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__48_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__48);
        v___x_1390_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__51;
        v___x_1391_ =
            l_Lean_addMacroScope(v_quotContext_1327_, v___x_1390_, v_currMacroScope_1328_);
        v___x_1392_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__53;
        v___x_1393_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1393_, 0, v___x_1331_);
        leanh::lean_ctor_set(v___x_1393_, 1, v___x_1389_);
        leanh::lean_ctor_set(v___x_1393_, 2, v___x_1391_);
        leanh::lean_ctor_set(v___x_1393_, 3, v___x_1392_);
        v___x_1394_ = l_Lean_Syntax_node3(
            v___x_1331_,
            v___x_1370_,
            v___x_1349_,
            v___x_1349_,
            v___x_1393_,
        );
        v___x_1395_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__55;
        v___x_1396_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__56;
        v___x_1397_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1397_, 0, v___x_1331_);
        leanh::lean_ctor_set(v___x_1397_, 1, v___x_1396_);
        v___x_1398_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1395_, v___x_1397_);
        v___x_1399_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58);
        v___x_1400_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__59;
        v___x_1401_ =
            l_Lean_addMacroScope(v_quotContext_1327_, v___x_1400_, v_currMacroScope_1328_);
        v___x_1402_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1402_, 0, v___x_1331_);
        leanh::lean_ctor_set(v___x_1402_, 1, v___x_1399_);
        leanh::lean_ctor_set(v___x_1402_, 2, v___x_1401_);
        leanh::lean_ctor_set(v___x_1402_, 3, v___x_1344_);
        v___x_1403_ = l_Lean_Syntax_node3(
            v___x_1331_,
            v___x_1370_,
            v___x_1349_,
            v___x_1349_,
            v___x_1402_,
        );
        v___x_1404_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61);
        v___x_1405_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__62;
        v___x_1406_ =
            l_Lean_addMacroScope(v_quotContext_1327_, v___x_1405_, v_currMacroScope_1328_);
        v___x_1407_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1407_, 0, v___x_1331_);
        leanh::lean_ctor_set(v___x_1407_, 1, v___x_1404_);
        leanh::lean_ctor_set(v___x_1407_, 2, v___x_1406_);
        leanh::lean_ctor_set(v___x_1407_, 3, v___x_1344_);
        v___x_1408_ = l_Lean_Syntax_node3(
            v___x_1331_,
            v___x_1370_,
            v___x_1349_,
            v___x_1349_,
            v___x_1407_,
        );
        v___x_1409_ = leanh::lean_unsigned_to_nat(11);
        v___x_1410_ = lean_mk_empty_array_with_capacity(v___x_1409_);
        v___x_1411_ = lean_array_push(v___x_1410_, v___x_1376_);
        leanh::lean_inc_ref_n(v___x_1378_, 4);
        v___x_1412_ = lean_array_push(v___x_1411_, v___x_1378_);
        v___x_1413_ = lean_array_push(v___x_1412_, v___x_1388_);
        v___x_1414_ = lean_array_push(v___x_1413_, v___x_1378_);
        v___x_1415_ = lean_array_push(v___x_1414_, v___x_1394_);
        v___x_1416_ = lean_array_push(v___x_1415_, v___x_1378_);
        v___x_1417_ = lean_array_push(v___x_1416_, v___x_1398_);
        v___x_1418_ = lean_array_push(v___x_1417_, v___x_1378_);
        v___x_1419_ = lean_array_push(v___x_1418_, v___x_1403_);
        v___x_1420_ = lean_array_push(v___x_1419_, v___x_1378_);
        v___x_1421_ = lean_array_push(v___x_1420_, v___x_1408_);
        v___x_1422_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_1422_, 0, v___x_1331_);
        leanh::lean_ctor_set(v___x_1422_, 1, v___x_1337_);
        leanh::lean_ctor_set(v___x_1422_, 2, v___x_1421_);
        v___x_1423_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__63;
        v___x_1424_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1424_, 0, v___x_1331_);
        leanh::lean_ctor_set(v___x_1424_, 1, v___x_1423_);
        v___x_1425_ = l_Lean_Syntax_node3(
            v___x_1331_,
            v___x_1337_,
            v___x_1369_,
            v___x_1422_,
            v___x_1424_,
        );
        v___x_1426_ = l_Lean_Syntax_node6(
            v___x_1331_,
            v___x_1361_,
            v___x_1362_,
            v___x_1364_,
            v___x_1349_,
            v___x_1367_,
            v___x_1425_,
            v___x_1349_,
        );
        v___x_1427_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1337_, v___x_1426_);
        v___x_1428_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1336_, v___x_1427_);
        v___x_1429_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1335_, v___x_1428_);
        v___x_1430_ = l_Lean_Syntax_node2(v___x_1331_, v___x_1357_, v___x_1359_, v___x_1429_);
        v___x_1431_ = l_Lean_Syntax_node5(
            v___x_1331_,
            v___x_1337_,
            v___x_1347_,
            v___x_1349_,
            v___x_1356_,
            v___x_1349_,
            v___x_1430_,
        );
        v___x_1432_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1336_, v___x_1431_);
        v___x_1433_ = l_Lean_Syntax_node1(v___x_1331_, v___x_1335_, v___x_1432_);
        v___x_1434_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64;
        v___x_1435_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1435_, 0, v___x_1331_);
        leanh::lean_ctor_set(v___x_1435_, 1, v___x_1434_);
        v___x_1436_ = l_Lean_Syntax_node3(
            v___x_1331_,
            v___x_1332_,
            v___x_1334_,
            v___x_1433_,
            v___x_1435_,
        );
        v___x_1437_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1437_, 0, v___x_1436_);
        leanh::lean_ctor_set(v___x_1437_, 1, v_a_1322_);
        return v___x_1437_;
    }
}
pub unsafe fn l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___boxed(
    mut v_x_1438_: *mut leanh::LeanObject,
    mut v_a_1439_: *mut leanh::LeanObject,
    mut v_a_1440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1441_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1(v_x_1438_, v_a_1439_, v_a_1440_);
    leanh::lean_dec_ref(v_a_1439_);
    return v_res_1441_;
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1(
    mut v_x_1464_: *mut leanh::LeanObject,
    mut v_a_1465_: *mut leanh::LeanObject,
    mut v_a_1466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: u8 = 0;
    v___x_1467_ = l_tacticDeriving__LawfulEq__tactic__step___closed__1;
    v___x_1468_ = l_Lean_Syntax_isOfKind(v_x_1464_, v___x_1467_);
    if v___x_1468_ == 0 {
        let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1469_ = leanh::lean_box(1);
        v___x_1470_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1470_, 0, v___x_1469_);
        leanh::lean_ctor_set(v___x_1470_, 1, v_a_1466_);
        return v___x_1470_;
    } else {
        let mut v_ref_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1472_: u8 = 0;
        let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ref_1471_ = leanh::lean_ctor_get(v_a_1465_, 5);
        v___x_1472_ = 0;
        v___x_1473_ = l_Lean_SourceInfo_fromRef(v_ref_1471_, v___x_1472_);
        v___x_1474_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__0;
        v___x_1475_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1;
        leanh::lean_inc_n(v___x_1473_, 4);
        v___x_1476_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1476_, 0, v___x_1473_);
        leanh::lean_ctor_set(v___x_1476_, 1, v___x_1474_);
        v___x_1477_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11;
        v___x_1478_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__3;
        v___x_1479_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__4;
        v___x_1480_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1480_, 0, v___x_1473_);
        leanh::lean_ctor_set(v___x_1480_, 1, v___x_1479_);
        v___x_1481_ = l_Lean_Syntax_node1(v___x_1473_, v___x_1478_, v___x_1480_);
        v___x_1482_ = l_Lean_Syntax_node1(v___x_1473_, v___x_1477_, v___x_1481_);
        v___x_1483_ = l_Lean_Syntax_node2(v___x_1473_, v___x_1475_, v___x_1476_, v___x_1482_);
        v___x_1484_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1484_, 0, v___x_1483_);
        leanh::lean_ctor_set(v___x_1484_, 1, v_a_1466_);
        return v___x_1484_;
    }
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___boxed(
    mut v_x_1485_: *mut leanh::LeanObject,
    mut v_a_1486_: *mut leanh::LeanObject,
    mut v_a_1487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1488_ =
        l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1(
            v_x_1485_, v_a_1486_, v_a_1487_,
        );
    leanh::lean_dec_ref(v_a_1486_);
    return v_res_1488_;
}
pub unsafe fn _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1519_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__12;
    v___x_1520_ = l_String_toRawSubstring_x27(v___x_1519_);
    return v___x_1520_;
}
pub unsafe fn _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1544_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__22;
    v___x_1545_ = l_String_toRawSubstring_x27(v___x_1544_);
    return v___x_1545_;
}
pub unsafe fn _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34()
-> *mut leanh::LeanObject {
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1564_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__33;
    v___x_1565_ = l_String_toRawSubstring_x27(v___x_1564_);
    return v___x_1565_;
}
pub unsafe fn _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__43()
-> *mut leanh::LeanObject {
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1585_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__42;
    v___x_1586_ = l_String_toRawSubstring_x27(v___x_1585_);
    return v___x_1586_;
}
pub unsafe fn _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67()
-> *mut leanh::LeanObject {
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1631_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__66;
    v___x_1632_ = l_String_toRawSubstring_x27(v___x_1631_);
    return v___x_1632_;
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2(
    mut v_x_1647_: *mut leanh::LeanObject,
    mut v_a_1648_: *mut leanh::LeanObject,
    mut v_a_1649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: u8 = 0;
    v___x_1650_ = l_tacticDeriving__LawfulEq__tactic__step___closed__1;
    v___x_1651_ = l_Lean_Syntax_isOfKind(v_x_1647_, v___x_1650_);
    if v___x_1651_ == 0 {
        let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1652_ = leanh::lean_box(1);
        v___x_1653_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1653_, 0, v___x_1652_);
        leanh::lean_ctor_set(v___x_1653_, 1, v_a_1649_);
        return v___x_1653_;
    } else {
        let mut v_quotContext_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1657_: u8 = 0;
        let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
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
        let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1654_ = leanh::lean_ctor_get(v_a_1648_, 1);
        v_currMacroScope_1655_ = leanh::lean_ctor_get(v_a_1648_, 2);
        v_ref_1656_ = leanh::lean_ctor_get(v_a_1648_, 5);
        v___x_1657_ = 0;
        v___x_1658_ = l_Lean_SourceInfo_fromRef(v_ref_1656_, v___x_1657_);
        v___x_1659_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4;
        v___x_1660_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5;
        leanh::lean_inc_n(v___x_1658_, 80);
        v___x_1661_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1661_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1661_, 1, v___x_1660_);
        v___x_1662_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7;
        v___x_1663_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9;
        v___x_1664_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11;
        v___x_1665_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1;
        v___x_1666_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__2;
        v___x_1667_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1667_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1667_, 1, v___x_1666_);
        v___x_1668_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__3;
        v___x_1669_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4;
        v___x_1670_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1670_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1670_, 1, v___x_1668_);
        v___x_1671_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7;
        v___x_1672_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__9;
        v___x_1673_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11;
        v___x_1674_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__13), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__13_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__13);
        v___x_1675_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__14;
        leanh::lean_inc_n(v_currMacroScope_1655_, 5);
        leanh::lean_inc_n(v_quotContext_1654_, 5);
        v___x_1676_ =
            l_Lean_addMacroScope(v_quotContext_1654_, v___x_1675_, v_currMacroScope_1655_);
        v___x_1677_ = leanh::lean_box(0);
        v___x_1678_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__16;
        v___x_1679_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1679_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1679_, 1, v___x_1674_);
        leanh::lean_ctor_set(v___x_1679_, 2, v___x_1676_);
        leanh::lean_ctor_set(v___x_1679_, 3, v___x_1678_);
        v___x_1680_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17;
        v___x_1681_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19;
        v___x_1682_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__21;
        v___x_1683_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23);
        v___x_1684_ = leanh::lean_box(0);
        v___x_1685_ =
            l_Lean_addMacroScope(v_quotContext_1654_, v___x_1684_, v_currMacroScope_1655_);
        v___x_1686_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__25;
        v___x_1687_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1687_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1687_, 1, v___x_1683_);
        leanh::lean_ctor_set(v___x_1687_, 2, v___x_1685_);
        leanh::lean_ctor_set(v___x_1687_, 3, v___x_1686_);
        v___x_1688_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1682_, v___x_1687_);
        leanh::lean_inc_ref(v___x_1661_);
        v___x_1689_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1681_, v___x_1661_, v___x_1688_);
        v___x_1690_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__27;
        v___x_1691_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29;
        v___x_1692_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__30;
        v___x_1693_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1693_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1693_, 1, v___x_1692_);
        leanh::lean_inc_ref(v___x_1693_);
        v___x_1694_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1691_, v___x_1693_);
        v___x_1695_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__31;
        v___x_1696_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1696_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1696_, 1, v___x_1695_);
        leanh::lean_inc_n(v___x_1694_, 4);
        v___x_1697_ = l_Lean_Syntax_node3(
            v___x_1658_,
            v___x_1690_,
            v___x_1694_,
            v___x_1696_,
            v___x_1694_,
        );
        v___x_1698_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64;
        v___x_1699_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1699_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1699_, 1, v___x_1698_);
        leanh::lean_inc_ref(v___x_1699_);
        v___x_1700_ = l_Lean_Syntax_node3(
            v___x_1658_,
            v___x_1680_,
            v___x_1689_,
            v___x_1697_,
            v___x_1699_,
        );
        v___x_1701_ = l_Lean_Syntax_node3(
            v___x_1658_,
            v___x_1664_,
            v___x_1700_,
            v___x_1694_,
            v___x_1694_,
        );
        v___x_1702_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1673_, v___x_1679_, v___x_1701_);
        v___x_1703_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__32;
        v___x_1704_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1704_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1704_, 1, v___x_1703_);
        v___x_1705_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34);
        v___x_1706_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__35;
        v___x_1707_ =
            l_Lean_addMacroScope(v_quotContext_1654_, v___x_1706_, v_currMacroScope_1655_);
        v___x_1708_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__38;
        v___x_1709_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1709_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1709_, 1, v___x_1705_);
        leanh::lean_ctor_set(v___x_1709_, 2, v___x_1707_);
        leanh::lean_ctor_set(v___x_1709_, 3, v___x_1708_);
        v___x_1710_ = l_Lean_Syntax_node3(
            v___x_1658_,
            v___x_1672_,
            v___x_1702_,
            v___x_1704_,
            v___x_1709_,
        );
        v___x_1711_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__39;
        v___x_1712_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1712_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1712_, 1, v___x_1711_);
        v___x_1713_ = l_Lean_Syntax_node3(
            v___x_1658_,
            v___x_1671_,
            v___x_1710_,
            v___x_1712_,
            v___x_1694_,
        );
        v___x_1714_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17);
        v___x_1715_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_1715_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1715_, 1, v___x_1664_);
        leanh::lean_ctor_set(v___x_1715_, 2, v___x_1714_);
        leanh::lean_inc_ref_n(v___x_1715_, 19);
        v___x_1716_ = l_Lean_Syntax_node3(
            v___x_1658_,
            v___x_1669_,
            v___x_1670_,
            v___x_1713_,
            v___x_1715_,
        );
        v___x_1717_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1664_, v___x_1716_);
        v___x_1718_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1663_, v___x_1717_);
        v___x_1719_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1662_, v___x_1718_);
        v___x_1720_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1665_, v___x_1667_, v___x_1719_);
        v___x_1721_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__40;
        v___x_1722_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41;
        v___x_1723_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1723_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1723_, 1, v___x_1721_);
        v___x_1724_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__43), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__43_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__43);
        v___x_1725_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__45;
        v___x_1726_ =
            l_Lean_addMacroScope(v_quotContext_1654_, v___x_1725_, v_currMacroScope_1655_);
        v___x_1727_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__47;
        v___x_1728_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1728_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1728_, 1, v___x_1724_);
        leanh::lean_ctor_set(v___x_1728_, 2, v___x_1726_);
        leanh::lean_ctor_set(v___x_1728_, 3, v___x_1727_);
        v___x_1729_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49;
        v___x_1730_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__50;
        v___x_1731_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1731_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1731_, 1, v___x_1730_);
        v___x_1732_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1729_, v___x_1731_, v___x_1693_);
        leanh::lean_inc(v___x_1732_);
        v___x_1733_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1664_, v___x_1732_, v___x_1732_);
        v___x_1734_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1673_, v___x_1728_, v___x_1733_);
        v___x_1735_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1722_, v___x_1723_, v___x_1734_);
        v___x_1736_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__52;
        v___x_1737_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__54;
        v___x_1738_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__55;
        v___x_1739_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1739_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1739_, 1, v___x_1738_);
        v___x_1740_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1737_, v___x_1739_);
        v___x_1741_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__57;
        v___x_1742_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__58;
        v___x_1743_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1743_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1743_, 1, v___x_1742_);
        v___x_1744_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__60;
        v___x_1745_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__61;
        v___x_1746_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1746_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1746_, 1, v___x_1745_);
        v___x_1747_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63;
        v___x_1748_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__64;
        v___x_1749_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1749_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1749_, 1, v___x_1748_);
        v___x_1750_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28;
        v___x_1751_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1750_, v___x_1715_);
        leanh::lean_inc_n(v___x_1751_, 2);
        v___x_1752_ = l_Lean_Syntax_node5(
            v___x_1658_,
            v___x_1747_,
            v___x_1749_,
            v___x_1751_,
            v___x_1715_,
            v___x_1715_,
            v___x_1715_,
        );
        v___x_1753_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1664_, v___x_1752_);
        v___x_1754_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1663_, v___x_1753_);
        v___x_1755_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1662_, v___x_1754_);
        leanh::lean_inc_ref_n(v___x_1746_, 2);
        v___x_1756_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1744_, v___x_1746_, v___x_1755_);
        v___x_1757_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25;
        v___x_1758_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26;
        v___x_1759_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1759_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1759_, 1, v___x_1757_);
        v___x_1760_ = l_Lean_Syntax_node6(
            v___x_1658_,
            v___x_1758_,
            v___x_1759_,
            v___x_1751_,
            v___x_1715_,
            v___x_1715_,
            v___x_1715_,
            v___x_1715_,
        );
        v___x_1761_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1664_, v___x_1760_);
        v___x_1762_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1663_, v___x_1761_);
        v___x_1763_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1662_, v___x_1762_);
        v___x_1764_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1744_, v___x_1746_, v___x_1763_);
        v___x_1765_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__0;
        v___x_1766_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1;
        v___x_1767_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1767_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1767_, 1, v___x_1765_);
        v___x_1768_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__3;
        v___x_1769_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__65;
        v___x_1770_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1770_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1770_, 1, v___x_1769_);
        v___x_1771_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1768_, v___x_1770_);
        v___x_1772_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1664_, v___x_1771_);
        v___x_1773_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1766_, v___x_1767_, v___x_1772_);
        v___x_1774_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1664_, v___x_1773_);
        v___x_1775_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1663_, v___x_1774_);
        v___x_1776_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1662_, v___x_1775_);
        v___x_1777_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1744_, v___x_1746_, v___x_1776_);
        v___x_1778_ = l_Lean_Syntax_node3(
            v___x_1658_,
            v___x_1664_,
            v___x_1756_,
            v___x_1764_,
            v___x_1777_,
        );
        v___x_1779_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1741_, v___x_1743_, v___x_1778_);
        v___x_1780_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1664_, v___x_1779_);
        v___x_1781_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1663_, v___x_1780_);
        v___x_1782_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1662_, v___x_1781_);
        v___x_1783_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1736_, v___x_1740_, v___x_1782_);
        v___x_1784_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12;
        v___x_1785_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13;
        v___x_1786_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1786_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1786_, 1, v___x_1784_);
        v___x_1787_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67);
        v___x_1788_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__68;
        v___x_1789_ =
            l_Lean_addMacroScope(v_quotContext_1654_, v___x_1788_, v_currMacroScope_1655_);
        v___x_1790_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1790_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1790_, 1, v___x_1787_);
        leanh::lean_ctor_set(v___x_1790_, 2, v___x_1789_);
        leanh::lean_ctor_set(v___x_1790_, 3, v___x_1677_);
        leanh::lean_inc_ref(v___x_1790_);
        v___x_1791_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1664_, v___x_1790_);
        v___x_1792_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1785_, v___x_1786_, v___x_1791_);
        v___x_1793_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__69;
        v___x_1794_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70;
        v___x_1795_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1795_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1795_, 1, v___x_1793_);
        v___x_1796_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21;
        v___x_1797_ = l_Lean_Syntax_node2(v___x_1658_, v___x_1796_, v___x_1715_, v___x_1790_);
        v___x_1798_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1664_, v___x_1797_);
        v___x_1799_ = l_Lean_Syntax_node4(
            v___x_1658_,
            v___x_1794_,
            v___x_1795_,
            v___x_1798_,
            v___x_1715_,
            v___x_1715_,
        );
        v___x_1800_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__71;
        v___x_1801_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__72;
        v___x_1802_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1802_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1802_, 1, v___x_1800_);
        v___x_1803_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__29;
        v___x_1804_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1804_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1804_, 1, v___x_1803_);
        v___x_1805_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1664_, v___x_1804_);
        v___x_1806_ = l_Lean_Syntax_node6(
            v___x_1658_,
            v___x_1801_,
            v___x_1802_,
            v___x_1751_,
            v___x_1715_,
            v___x_1805_,
            v___x_1715_,
            v___x_1715_,
        );
        v___x_1807_ = leanh::lean_unsigned_to_nat(11);
        v___x_1808_ = lean_mk_empty_array_with_capacity(v___x_1807_);
        v___x_1809_ = lean_array_push(v___x_1808_, v___x_1720_);
        v___x_1810_ = lean_array_push(v___x_1809_, v___x_1715_);
        v___x_1811_ = lean_array_push(v___x_1810_, v___x_1735_);
        v___x_1812_ = lean_array_push(v___x_1811_, v___x_1715_);
        v___x_1813_ = lean_array_push(v___x_1812_, v___x_1783_);
        v___x_1814_ = lean_array_push(v___x_1813_, v___x_1715_);
        v___x_1815_ = lean_array_push(v___x_1814_, v___x_1792_);
        v___x_1816_ = lean_array_push(v___x_1815_, v___x_1715_);
        v___x_1817_ = lean_array_push(v___x_1816_, v___x_1799_);
        v___x_1818_ = lean_array_push(v___x_1817_, v___x_1715_);
        v___x_1819_ = lean_array_push(v___x_1818_, v___x_1806_);
        v___x_1820_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_1820_, 0, v___x_1658_);
        leanh::lean_ctor_set(v___x_1820_, 1, v___x_1664_);
        leanh::lean_ctor_set(v___x_1820_, 2, v___x_1819_);
        v___x_1821_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1663_, v___x_1820_);
        v___x_1822_ = l_Lean_Syntax_node1(v___x_1658_, v___x_1662_, v___x_1821_);
        v___x_1823_ = l_Lean_Syntax_node3(
            v___x_1658_,
            v___x_1659_,
            v___x_1661_,
            v___x_1822_,
            v___x_1699_,
        );
        v___x_1824_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1824_, 0, v___x_1823_);
        leanh::lean_ctor_set(v___x_1824_, 1, v_a_1649_);
        return v___x_1824_;
    }
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___boxed(
    mut v_x_1825_: *mut leanh::LeanObject,
    mut v_a_1826_: *mut leanh::LeanObject,
    mut v_a_1827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1828_ =
        l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2(
            v_x_1825_, v_a_1826_, v_a_1827_,
        );
    leanh::lean_dec_ref(v_a_1826_);
    return v_res_1828_;
}
pub unsafe fn _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1839_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__3;
    v___x_1840_ = l_String_toRawSubstring_x27(v___x_1839_);
    return v___x_1840_;
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3(
    mut v_x_1857_: *mut leanh::LeanObject,
    mut v_a_1858_: *mut leanh::LeanObject,
    mut v_a_1859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: u8 = 0;
    v___x_1860_ = l_tacticDeriving__LawfulEq__tactic__step___closed__1;
    v___x_1861_ = l_Lean_Syntax_isOfKind(v_x_1857_, v___x_1860_);
    if v___x_1861_ == 0 {
        let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1862_ = leanh::lean_box(1);
        v___x_1863_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1863_, 0, v___x_1862_);
        leanh::lean_ctor_set(v___x_1863_, 1, v_a_1859_);
        return v___x_1863_;
    } else {
        let mut v_quotContext_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1867_: u8 = 0;
        let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1864_ = leanh::lean_ctor_get(v_a_1858_, 1);
        v_currMacroScope_1865_ = leanh::lean_ctor_get(v_a_1858_, 2);
        v_ref_1866_ = leanh::lean_ctor_get(v_a_1858_, 5);
        v___x_1867_ = 0;
        v___x_1868_ = l_Lean_SourceInfo_fromRef(v_ref_1866_, v___x_1867_);
        v___x_1869_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4;
        v___x_1870_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5;
        leanh::lean_inc_n(v___x_1868_, 71);
        v___x_1871_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1871_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1871_, 1, v___x_1870_);
        v___x_1872_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7;
        v___x_1873_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9;
        v___x_1874_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11;
        v___x_1875_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1;
        v___x_1876_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__2;
        v___x_1877_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1877_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1877_, 1, v___x_1876_);
        v___x_1878_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__3;
        v___x_1879_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4;
        v___x_1880_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1880_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1880_, 1, v___x_1878_);
        v___x_1881_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7;
        v___x_1882_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__9;
        v___x_1883_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17;
        v___x_1884_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19;
        v___x_1885_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__21;
        v___x_1886_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23);
        v___x_1887_ = leanh::lean_box(0);
        leanh::lean_inc_n(v_currMacroScope_1865_, 4);
        leanh::lean_inc_n(v_quotContext_1864_, 4);
        v___x_1888_ =
            l_Lean_addMacroScope(v_quotContext_1864_, v___x_1887_, v_currMacroScope_1865_);
        v___x_1889_ = leanh::lean_box(0);
        v___x_1890_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__0;
        v___x_1891_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1891_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1891_, 1, v___x_1886_);
        leanh::lean_ctor_set(v___x_1891_, 2, v___x_1888_);
        leanh::lean_ctor_set(v___x_1891_, 3, v___x_1890_);
        v___x_1892_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1885_, v___x_1891_);
        leanh::lean_inc_ref(v___x_1871_);
        v___x_1893_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1884_, v___x_1871_, v___x_1892_);
        v___x_1894_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__27;
        v___x_1895_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29;
        v___x_1896_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__30;
        v___x_1897_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1897_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1897_, 1, v___x_1896_);
        leanh::lean_inc_ref(v___x_1897_);
        v___x_1898_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1895_, v___x_1897_);
        v___x_1899_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__31;
        v___x_1900_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1900_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1900_, 1, v___x_1899_);
        leanh::lean_inc_n(v___x_1898_, 2);
        v___x_1901_ = l_Lean_Syntax_node3(
            v___x_1868_,
            v___x_1894_,
            v___x_1898_,
            v___x_1900_,
            v___x_1898_,
        );
        v___x_1902_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64;
        v___x_1903_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1903_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1903_, 1, v___x_1902_);
        leanh::lean_inc_ref(v___x_1903_);
        v___x_1904_ = l_Lean_Syntax_node3(
            v___x_1868_,
            v___x_1883_,
            v___x_1893_,
            v___x_1901_,
            v___x_1903_,
        );
        v___x_1905_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__32;
        v___x_1906_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1906_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1906_, 1, v___x_1905_);
        v___x_1907_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34);
        v___x_1908_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__35;
        v___x_1909_ =
            l_Lean_addMacroScope(v_quotContext_1864_, v___x_1908_, v_currMacroScope_1865_);
        v___x_1910_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__2;
        v___x_1911_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1911_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1911_, 1, v___x_1907_);
        leanh::lean_ctor_set(v___x_1911_, 2, v___x_1909_);
        leanh::lean_ctor_set(v___x_1911_, 3, v___x_1910_);
        v___x_1912_ = l_Lean_Syntax_node3(
            v___x_1868_,
            v___x_1882_,
            v___x_1904_,
            v___x_1906_,
            v___x_1911_,
        );
        v___x_1913_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__39;
        v___x_1914_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1914_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1914_, 1, v___x_1913_);
        v___x_1915_ = l_Lean_Syntax_node3(
            v___x_1868_,
            v___x_1881_,
            v___x_1912_,
            v___x_1914_,
            v___x_1898_,
        );
        v___x_1916_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17);
        v___x_1917_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_1917_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1917_, 1, v___x_1874_);
        leanh::lean_ctor_set(v___x_1917_, 2, v___x_1916_);
        leanh::lean_inc_ref_n(v___x_1917_, 12);
        v___x_1918_ = l_Lean_Syntax_node3(
            v___x_1868_,
            v___x_1879_,
            v___x_1880_,
            v___x_1915_,
            v___x_1917_,
        );
        v___x_1919_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1874_, v___x_1918_);
        v___x_1920_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1873_, v___x_1919_);
        v___x_1921_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1872_, v___x_1920_);
        v___x_1922_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1875_, v___x_1877_, v___x_1921_);
        v___x_1923_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__40;
        v___x_1924_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41;
        v___x_1925_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1925_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1925_, 1, v___x_1923_);
        v___x_1926_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11;
        v___x_1927_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__4), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__4_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__4);
        v___x_1928_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__6;
        v___x_1929_ =
            l_Lean_addMacroScope(v_quotContext_1864_, v___x_1928_, v_currMacroScope_1865_);
        v___x_1930_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__8;
        v___x_1931_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1931_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1931_, 1, v___x_1927_);
        leanh::lean_ctor_set(v___x_1931_, 2, v___x_1929_);
        leanh::lean_ctor_set(v___x_1931_, 3, v___x_1930_);
        v___x_1932_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49;
        v___x_1933_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__50;
        v___x_1934_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1934_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1934_, 1, v___x_1933_);
        v___x_1935_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1932_, v___x_1934_, v___x_1897_);
        leanh::lean_inc(v___x_1935_);
        v___x_1936_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1874_, v___x_1935_, v___x_1935_);
        v___x_1937_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1926_, v___x_1931_, v___x_1936_);
        v___x_1938_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1924_, v___x_1925_, v___x_1937_);
        v___x_1939_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__52;
        v___x_1940_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__54;
        v___x_1941_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__55;
        v___x_1942_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1942_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1942_, 1, v___x_1941_);
        v___x_1943_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1940_, v___x_1942_);
        v___x_1944_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__57;
        v___x_1945_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__58;
        v___x_1946_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1946_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1946_, 1, v___x_1945_);
        v___x_1947_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__60;
        v___x_1948_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__61;
        v___x_1949_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1949_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1949_, 1, v___x_1948_);
        v___x_1950_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__63;
        v___x_1951_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__64;
        v___x_1952_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1952_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1952_, 1, v___x_1951_);
        v___x_1953_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28;
        v___x_1954_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1953_, v___x_1917_);
        leanh::lean_inc(v___x_1954_);
        v___x_1955_ = l_Lean_Syntax_node5(
            v___x_1868_,
            v___x_1950_,
            v___x_1952_,
            v___x_1954_,
            v___x_1917_,
            v___x_1917_,
            v___x_1917_,
        );
        v___x_1956_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1874_, v___x_1955_);
        v___x_1957_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1873_, v___x_1956_);
        v___x_1958_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1872_, v___x_1957_);
        leanh::lean_inc_ref_n(v___x_1949_, 2);
        v___x_1959_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1947_, v___x_1949_, v___x_1958_);
        v___x_1960_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25;
        v___x_1961_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26;
        v___x_1962_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1962_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1962_, 1, v___x_1960_);
        v___x_1963_ = l_Lean_Syntax_node6(
            v___x_1868_,
            v___x_1961_,
            v___x_1962_,
            v___x_1954_,
            v___x_1917_,
            v___x_1917_,
            v___x_1917_,
            v___x_1917_,
        );
        v___x_1964_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1874_, v___x_1963_);
        v___x_1965_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1873_, v___x_1964_);
        v___x_1966_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1872_, v___x_1965_);
        v___x_1967_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1947_, v___x_1949_, v___x_1966_);
        v___x_1968_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__0;
        v___x_1969_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__1;
        v___x_1970_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1970_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1970_, 1, v___x_1968_);
        v___x_1971_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__1___closed__3;
        v___x_1972_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__65;
        v___x_1973_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1973_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1973_, 1, v___x_1972_);
        v___x_1974_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1971_, v___x_1973_);
        v___x_1975_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1874_, v___x_1974_);
        v___x_1976_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1969_, v___x_1970_, v___x_1975_);
        v___x_1977_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1874_, v___x_1976_);
        v___x_1978_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1873_, v___x_1977_);
        v___x_1979_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1872_, v___x_1978_);
        v___x_1980_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1947_, v___x_1949_, v___x_1979_);
        v___x_1981_ = l_Lean_Syntax_node3(
            v___x_1868_,
            v___x_1874_,
            v___x_1959_,
            v___x_1967_,
            v___x_1980_,
        );
        v___x_1982_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1944_, v___x_1946_, v___x_1981_);
        v___x_1983_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1874_, v___x_1982_);
        v___x_1984_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1873_, v___x_1983_);
        v___x_1985_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1872_, v___x_1984_);
        v___x_1986_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1939_, v___x_1943_, v___x_1985_);
        v___x_1987_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12;
        v___x_1988_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13;
        v___x_1989_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1989_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1989_, 1, v___x_1987_);
        v___x_1990_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__67);
        v___x_1991_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__68;
        v___x_1992_ =
            l_Lean_addMacroScope(v_quotContext_1864_, v___x_1991_, v_currMacroScope_1865_);
        v___x_1993_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1993_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1993_, 1, v___x_1990_);
        leanh::lean_ctor_set(v___x_1993_, 2, v___x_1992_);
        leanh::lean_ctor_set(v___x_1993_, 3, v___x_1889_);
        v___x_1994_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1874_, v___x_1993_);
        leanh::lean_inc(v___x_1994_);
        v___x_1995_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1988_, v___x_1989_, v___x_1994_);
        v___x_1996_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__9;
        v___x_1997_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__10;
        v___x_1998_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1998_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_1998_, 1, v___x_1996_);
        v___x_1999_ = l_Lean_Syntax_node2(v___x_1868_, v___x_1997_, v___x_1998_, v___x_1994_);
        v___x_2000_ = leanh::lean_unsigned_to_nat(9);
        v___x_2001_ = lean_mk_empty_array_with_capacity(v___x_2000_);
        v___x_2002_ = lean_array_push(v___x_2001_, v___x_1922_);
        v___x_2003_ = lean_array_push(v___x_2002_, v___x_1917_);
        v___x_2004_ = lean_array_push(v___x_2003_, v___x_1938_);
        v___x_2005_ = lean_array_push(v___x_2004_, v___x_1917_);
        v___x_2006_ = lean_array_push(v___x_2005_, v___x_1986_);
        v___x_2007_ = lean_array_push(v___x_2006_, v___x_1917_);
        v___x_2008_ = lean_array_push(v___x_2007_, v___x_1995_);
        v___x_2009_ = lean_array_push(v___x_2008_, v___x_1917_);
        v___x_2010_ = lean_array_push(v___x_2009_, v___x_1999_);
        v___x_2011_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_2011_, 0, v___x_1868_);
        leanh::lean_ctor_set(v___x_2011_, 1, v___x_1874_);
        leanh::lean_ctor_set(v___x_2011_, 2, v___x_2010_);
        v___x_2012_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1873_, v___x_2011_);
        v___x_2013_ = l_Lean_Syntax_node1(v___x_1868_, v___x_1872_, v___x_2012_);
        v___x_2014_ = l_Lean_Syntax_node3(
            v___x_1868_,
            v___x_1869_,
            v___x_1871_,
            v___x_2013_,
            v___x_1903_,
        );
        v___x_2015_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2015_, 0, v___x_2014_);
        leanh::lean_ctor_set(v___x_2015_, 1, v_a_1859_);
        return v___x_2015_;
    }
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___boxed(
    mut v_x_2016_: *mut leanh::LeanObject,
    mut v_a_2017_: *mut leanh::LeanObject,
    mut v_a_2018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2019_ =
        l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3(
            v_x_2016_, v_a_2017_, v_a_2018_,
        );
    leanh::lean_dec_ref(v_a_2017_);
    return v_res_2019_;
}
pub unsafe fn _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2025_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__3;
    v___x_2026_ = l_String_toRawSubstring_x27(v___x_2025_);
    return v___x_2026_;
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4(
    mut v_x_2037_: *mut leanh::LeanObject,
    mut v_a_2038_: *mut leanh::LeanObject,
    mut v_a_2039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: u8 = 0;
    v___x_2040_ = l_tacticDeriving__LawfulEq__tactic__step___closed__1;
    v___x_2041_ = l_Lean_Syntax_isOfKind(v_x_2037_, v___x_2040_);
    if v___x_2041_ == 0 {
        let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2042_ = leanh::lean_box(1);
        v___x_2043_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2043_, 0, v___x_2042_);
        leanh::lean_ctor_set(v___x_2043_, 1, v_a_2039_);
        return v___x_2043_;
    } else {
        let mut v_quotContext_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2047_: u8 = 0;
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
        let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2044_ = leanh::lean_ctor_get(v_a_2038_, 1);
        v_currMacroScope_2045_ = leanh::lean_ctor_get(v_a_2038_, 2);
        v_ref_2046_ = leanh::lean_ctor_get(v_a_2038_, 5);
        v___x_2047_ = 0;
        v___x_2048_ = l_Lean_SourceInfo_fromRef(v_ref_2046_, v___x_2047_);
        v___x_2049_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4;
        v___x_2050_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5;
        leanh::lean_inc_n(v___x_2048_, 35);
        v___x_2051_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2051_, 0, v___x_2048_);
        leanh::lean_ctor_set(v___x_2051_, 1, v___x_2050_);
        v___x_2052_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7;
        v___x_2053_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9;
        v___x_2054_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11;
        v___x_2055_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__1;
        v___x_2056_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__2;
        v___x_2057_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2057_, 0, v___x_2048_);
        leanh::lean_ctor_set(v___x_2057_, 1, v___x_2056_);
        v___x_2058_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__3;
        v___x_2059_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__4;
        v___x_2060_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2060_, 0, v___x_2048_);
        leanh::lean_ctor_set(v___x_2060_, 1, v___x_2058_);
        v___x_2061_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__7;
        v___x_2062_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__9;
        v___x_2063_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__17;
        v___x_2064_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__19;
        v___x_2065_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__21;
        v___x_2066_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__23);
        v___x_2067_ = leanh::lean_box(0);
        leanh::lean_inc_n(v_currMacroScope_2045_, 3);
        leanh::lean_inc_n(v_quotContext_2044_, 3);
        v___x_2068_ =
            l_Lean_addMacroScope(v_quotContext_2044_, v___x_2067_, v_currMacroScope_2045_);
        v___x_2069_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__0;
        v___x_2070_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2070_, 0, v___x_2048_);
        leanh::lean_ctor_set(v___x_2070_, 1, v___x_2066_);
        leanh::lean_ctor_set(v___x_2070_, 2, v___x_2068_);
        leanh::lean_ctor_set(v___x_2070_, 3, v___x_2069_);
        v___x_2071_ = l_Lean_Syntax_node1(v___x_2048_, v___x_2065_, v___x_2070_);
        leanh::lean_inc_ref(v___x_2051_);
        v___x_2072_ = l_Lean_Syntax_node2(v___x_2048_, v___x_2064_, v___x_2051_, v___x_2071_);
        v___x_2073_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__1;
        v___x_2074_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__27;
        v___x_2075_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29;
        v___x_2076_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__30;
        v___x_2077_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2077_, 0, v___x_2048_);
        leanh::lean_ctor_set(v___x_2077_, 1, v___x_2076_);
        leanh::lean_inc_ref(v___x_2077_);
        v___x_2078_ = l_Lean_Syntax_node1(v___x_2048_, v___x_2075_, v___x_2077_);
        v___x_2079_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__31;
        v___x_2080_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2080_, 0, v___x_2048_);
        leanh::lean_ctor_set(v___x_2080_, 1, v___x_2079_);
        leanh::lean_inc_n(v___x_2078_, 3);
        v___x_2081_ = l_Lean_Syntax_node3(
            v___x_2048_,
            v___x_2074_,
            v___x_2078_,
            v___x_2080_,
            v___x_2078_,
        );
        v___x_2082_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__2;
        v___x_2083_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2083_, 0, v___x_2048_);
        leanh::lean_ctor_set(v___x_2083_, 1, v___x_2082_);
        v___x_2084_ = l_Lean_Syntax_node3(
            v___x_2048_,
            v___x_2073_,
            v___x_2081_,
            v___x_2083_,
            v___x_2078_,
        );
        v___x_2085_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64;
        v___x_2086_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2086_, 0, v___x_2048_);
        leanh::lean_ctor_set(v___x_2086_, 1, v___x_2085_);
        leanh::lean_inc_ref(v___x_2086_);
        v___x_2087_ = l_Lean_Syntax_node3(
            v___x_2048_,
            v___x_2063_,
            v___x_2072_,
            v___x_2084_,
            v___x_2086_,
        );
        v___x_2088_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__32;
        v___x_2089_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2089_, 0, v___x_2048_);
        leanh::lean_ctor_set(v___x_2089_, 1, v___x_2088_);
        v___x_2090_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__34);
        v___x_2091_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__35;
        v___x_2092_ =
            l_Lean_addMacroScope(v_quotContext_2044_, v___x_2091_, v_currMacroScope_2045_);
        v___x_2093_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__3___closed__2;
        v___x_2094_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2094_, 0, v___x_2048_);
        leanh::lean_ctor_set(v___x_2094_, 1, v___x_2090_);
        leanh::lean_ctor_set(v___x_2094_, 2, v___x_2092_);
        leanh::lean_ctor_set(v___x_2094_, 3, v___x_2093_);
        v___x_2095_ = l_Lean_Syntax_node3(
            v___x_2048_,
            v___x_2062_,
            v___x_2087_,
            v___x_2089_,
            v___x_2094_,
        );
        v___x_2096_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__39;
        v___x_2097_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2097_, 0, v___x_2048_);
        leanh::lean_ctor_set(v___x_2097_, 1, v___x_2096_);
        v___x_2098_ = l_Lean_Syntax_node3(
            v___x_2048_,
            v___x_2061_,
            v___x_2095_,
            v___x_2097_,
            v___x_2078_,
        );
        v___x_2099_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17);
        v___x_2100_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_2100_, 0, v___x_2048_);
        leanh::lean_ctor_set(v___x_2100_, 1, v___x_2054_);
        leanh::lean_ctor_set(v___x_2100_, 2, v___x_2099_);
        leanh::lean_inc_ref(v___x_2100_);
        v___x_2101_ = l_Lean_Syntax_node3(
            v___x_2048_,
            v___x_2059_,
            v___x_2060_,
            v___x_2098_,
            v___x_2100_,
        );
        v___x_2102_ = l_Lean_Syntax_node1(v___x_2048_, v___x_2054_, v___x_2101_);
        v___x_2103_ = l_Lean_Syntax_node1(v___x_2048_, v___x_2053_, v___x_2102_);
        v___x_2104_ = l_Lean_Syntax_node1(v___x_2048_, v___x_2052_, v___x_2103_);
        v___x_2105_ = l_Lean_Syntax_node2(v___x_2048_, v___x_2055_, v___x_2057_, v___x_2104_);
        v___x_2106_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__40;
        v___x_2107_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__41;
        v___x_2108_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2108_, 0, v___x_2048_);
        leanh::lean_ctor_set(v___x_2108_, 1, v___x_2106_);
        v___x_2109_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__11;
        v___x_2110_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__4), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__4_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__4);
        v___x_2111_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__6;
        v___x_2112_ =
            l_Lean_addMacroScope(v_quotContext_2044_, v___x_2111_, v_currMacroScope_2045_);
        v___x_2113_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___closed__8;
        v___x_2114_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2114_, 0, v___x_2048_);
        leanh::lean_ctor_set(v___x_2114_, 1, v___x_2110_);
        leanh::lean_ctor_set(v___x_2114_, 2, v___x_2112_);
        leanh::lean_ctor_set(v___x_2114_, 3, v___x_2113_);
        v___x_2115_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__49;
        v___x_2116_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__50;
        v___x_2117_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2117_, 0, v___x_2048_);
        leanh::lean_ctor_set(v___x_2117_, 1, v___x_2116_);
        v___x_2118_ = l_Lean_Syntax_node2(v___x_2048_, v___x_2115_, v___x_2117_, v___x_2077_);
        v___x_2119_ = l_Lean_Syntax_node1(v___x_2048_, v___x_2054_, v___x_2118_);
        v___x_2120_ = l_Lean_Syntax_node2(v___x_2048_, v___x_2109_, v___x_2114_, v___x_2119_);
        v___x_2121_ = l_Lean_Syntax_node2(v___x_2048_, v___x_2107_, v___x_2108_, v___x_2120_);
        v___x_2122_ = l_Lean_Syntax_node3(
            v___x_2048_,
            v___x_2054_,
            v___x_2105_,
            v___x_2100_,
            v___x_2121_,
        );
        v___x_2123_ = l_Lean_Syntax_node1(v___x_2048_, v___x_2053_, v___x_2122_);
        v___x_2124_ = l_Lean_Syntax_node1(v___x_2048_, v___x_2052_, v___x_2123_);
        v___x_2125_ = l_Lean_Syntax_node3(
            v___x_2048_,
            v___x_2049_,
            v___x_2051_,
            v___x_2124_,
            v___x_2086_,
        );
        v___x_2126_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2126_, 0, v___x_2125_);
        leanh::lean_ctor_set(v___x_2126_, 1, v_a_2039_);
        return v___x_2126_;
    }
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4___boxed(
    mut v_x_2127_: *mut leanh::LeanObject,
    mut v_a_2128_: *mut leanh::LeanObject,
    mut v_a_2129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2130_ =
        l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__4(
            v_x_2127_, v_a_2128_, v_a_2129_,
        );
    leanh::lean_dec_ref(v_a_2128_);
    return v_res_2130_;
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5(
    mut v_x_2138_: *mut leanh::LeanObject,
    mut v_a_2139_: *mut leanh::LeanObject,
    mut v_a_2140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: u8 = 0;
    v___x_2141_ = l_tacticDeriving__LawfulEq__tactic__step___closed__1;
    v___x_2142_ = l_Lean_Syntax_isOfKind(v_x_2138_, v___x_2141_);
    if v___x_2142_ == 0 {
        let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2143_ = leanh::lean_box(1);
        v___x_2144_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2144_, 0, v___x_2143_);
        leanh::lean_ctor_set(v___x_2144_, 1, v_a_2140_);
        return v___x_2144_;
    } else {
        let mut v_ref_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2146_: u8 = 0;
        let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ref_2145_ = leanh::lean_ctor_get(v_a_2139_, 5);
        v___x_2146_ = 0;
        v___x_2147_ = l_Lean_SourceInfo_fromRef(v_ref_2145_, v___x_2146_);
        v___x_2148_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__1;
        v___x_2149_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___closed__2;
        leanh::lean_inc(v___x_2147_);
        v___x_2150_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2150_, 0, v___x_2147_);
        leanh::lean_ctor_set(v___x_2150_, 1, v___x_2149_);
        v___x_2151_ = l_Lean_Syntax_node1(v___x_2147_, v___x_2148_, v___x_2150_);
        v___x_2152_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2152_, 0, v___x_2151_);
        leanh::lean_ctor_set(v___x_2152_, 1, v_a_2140_);
        return v___x_2152_;
    }
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5___boxed(
    mut v_x_2153_: *mut leanh::LeanObject,
    mut v_a_2154_: *mut leanh::LeanObject,
    mut v_a_2155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2156_ =
        l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__5(
            v_x_2153_, v_a_2154_, v_a_2155_,
        );
    leanh::lean_dec_ref(v_a_2154_);
    return v_res_2156_;
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6(
    mut v_x_2171_: *mut leanh::LeanObject,
    mut v_a_2172_: *mut leanh::LeanObject,
    mut v_a_2173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: u8 = 0;
    v___x_2174_ = l_tacticDeriving__LawfulEq__tactic__step___closed__1;
    v___x_2175_ = l_Lean_Syntax_isOfKind(v_x_2171_, v___x_2174_);
    if v___x_2175_ == 0 {
        let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2176_ = leanh::lean_box(1);
        v___x_2177_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2177_, 0, v___x_2176_);
        leanh::lean_ctor_set(v___x_2177_, 1, v_a_2173_);
        return v___x_2177_;
    } else {
        let mut v_ref_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2179_: u8 = 0;
        let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ref_2178_ = leanh::lean_ctor_get(v_a_2172_, 5);
        v___x_2179_ = 0;
        v___x_2180_ = l_Lean_SourceInfo_fromRef(v_ref_2178_, v___x_2179_);
        v___x_2181_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__1;
        v___x_2182_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11;
        v___x_2183_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12;
        v___x_2184_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13;
        leanh::lean_inc_n(v___x_2180_, 9);
        v___x_2185_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2185_, 0, v___x_2180_);
        leanh::lean_ctor_set(v___x_2185_, 1, v___x_2183_);
        v___x_2186_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__29;
        v___x_2187_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__30;
        v___x_2188_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2188_, 0, v___x_2180_);
        leanh::lean_ctor_set(v___x_2188_, 1, v___x_2187_);
        v___x_2189_ = l_Lean_Syntax_node1(v___x_2180_, v___x_2186_, v___x_2188_);
        v___x_2190_ = l_Lean_Syntax_node1(v___x_2180_, v___x_2182_, v___x_2189_);
        v___x_2191_ = l_Lean_Syntax_node2(v___x_2180_, v___x_2184_, v___x_2185_, v___x_2190_);
        v___x_2192_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__2;
        v___x_2193_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2193_, 0, v___x_2180_);
        leanh::lean_ctor_set(v___x_2193_, 1, v___x_2192_);
        v___x_2194_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__4;
        v___x_2195_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___closed__5;
        v___x_2196_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2196_, 0, v___x_2180_);
        leanh::lean_ctor_set(v___x_2196_, 1, v___x_2195_);
        v___x_2197_ = l_Lean_Syntax_node1(v___x_2180_, v___x_2194_, v___x_2196_);
        v___x_2198_ = l_Lean_Syntax_node3(
            v___x_2180_,
            v___x_2182_,
            v___x_2191_,
            v___x_2193_,
            v___x_2197_,
        );
        v___x_2199_ = l_Lean_Syntax_node1(v___x_2180_, v___x_2181_, v___x_2198_);
        v___x_2200_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2200_, 0, v___x_2199_);
        leanh::lean_ctor_set(v___x_2200_, 1, v_a_2173_);
        return v___x_2200_;
    }
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6___boxed(
    mut v_x_2201_: *mut leanh::LeanObject,
    mut v_a_2202_: *mut leanh::LeanObject,
    mut v_a_2203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2204_ =
        l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__6(
            v_x_2201_, v_a_2202_, v_a_2203_,
        );
    leanh::lean_dec_ref(v_a_2202_);
    return v_res_2204_;
}
pub unsafe fn _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2218_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__0;
    v___x_2219_ = l_String_toRawSubstring_x27(v___x_2218_);
    return v___x_2219_;
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1(
    mut v_x_2229_: *mut leanh::LeanObject,
    mut v_a_2230_: *mut leanh::LeanObject,
    mut v_a_2231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: u8 = 0;
    v___x_2232_ = l_tacticDeriving__LawfulEq__tactic___closed__1;
    v___x_2233_ = l_Lean_Syntax_isOfKind(v_x_2229_, v___x_2232_);
    if v___x_2233_ == 0 {
        let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2234_ = leanh::lean_box(1);
        v___x_2235_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2235_, 0, v___x_2234_);
        leanh::lean_ctor_set(v___x_2235_, 1, v_a_2231_);
        return v___x_2235_;
    } else {
        let mut v_quotContext_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2239_: u8 = 0;
        let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2236_ = leanh::lean_ctor_get(v_a_2230_, 1);
        v_currMacroScope_2237_ = leanh::lean_ctor_get(v_a_2230_, 2);
        v_ref_2238_ = leanh::lean_ctor_get(v_a_2230_, 5);
        v___x_2239_ = 0;
        v___x_2240_ = l_Lean_SourceInfo_fromRef(v_ref_2238_, v___x_2239_);
        v___x_2241_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__4;
        v___x_2242_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__5;
        leanh::lean_inc_n(v___x_2240_, 51);
        v___x_2243_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2243_, 0, v___x_2240_);
        leanh::lean_ctor_set(v___x_2243_, 1, v___x_2242_);
        v___x_2244_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__7;
        v___x_2245_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__9;
        v___x_2246_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__11;
        v___x_2247_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__12;
        v___x_2248_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__13;
        v___x_2249_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2249_, 0, v___x_2240_);
        leanh::lean_ctor_set(v___x_2249_, 1, v___x_2247_);
        v___x_2250_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__15);
        v___x_2251_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__16;
        leanh::lean_inc_n(v_currMacroScope_2237_, 4);
        leanh::lean_inc_n(v_quotContext_2236_, 4);
        v___x_2252_ =
            l_Lean_addMacroScope(v_quotContext_2236_, v___x_2251_, v_currMacroScope_2237_);
        v___x_2253_ = leanh::lean_box(0);
        v___x_2254_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2254_, 0, v___x_2240_);
        leanh::lean_ctor_set(v___x_2254_, 1, v___x_2250_);
        leanh::lean_ctor_set(v___x_2254_, 2, v___x_2252_);
        leanh::lean_ctor_set(v___x_2254_, 3, v___x_2253_);
        leanh::lean_inc_ref(v___x_2254_);
        v___x_2255_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2246_, v___x_2254_);
        leanh::lean_inc_ref(v___x_2249_);
        v___x_2256_ = l_Lean_Syntax_node2(v___x_2240_, v___x_2248_, v___x_2249_, v___x_2255_);
        v___x_2257_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__17);
        v___x_2258_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_2258_, 0, v___x_2240_);
        leanh::lean_ctor_set(v___x_2258_, 1, v___x_2246_);
        leanh::lean_ctor_set(v___x_2258_, 2, v___x_2257_);
        v___x_2259_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__18;
        v___x_2260_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__19;
        v___x_2261_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2261_, 0, v___x_2240_);
        leanh::lean_ctor_set(v___x_2261_, 1, v___x_2259_);
        v___x_2262_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__21;
        leanh::lean_inc_ref_n(v___x_2258_, 18);
        v___x_2263_ = l_Lean_Syntax_node2(v___x_2240_, v___x_2262_, v___x_2258_, v___x_2254_);
        v___x_2264_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2246_, v___x_2263_);
        v___x_2265_ = l_Lean_Syntax_node5(
            v___x_2240_,
            v___x_2260_,
            v___x_2261_,
            v___x_2264_,
            v___x_2258_,
            v___x_2258_,
            v___x_2258_,
        );
        v___x_2266_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__23;
        v___x_2267_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__24;
        v___x_2268_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2268_, 0, v___x_2240_);
        leanh::lean_ctor_set(v___x_2268_, 1, v___x_2267_);
        v___x_2269_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__1), core::ptr::addr_of_mut!(l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__1_once), _init_l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__1);
        v___x_2270_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__2;
        v___x_2271_ =
            l_Lean_addMacroScope(v_quotContext_2236_, v___x_2270_, v_currMacroScope_2237_);
        v___x_2272_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2272_, 0, v___x_2240_);
        leanh::lean_ctor_set(v___x_2272_, 1, v___x_2269_);
        leanh::lean_ctor_set(v___x_2272_, 2, v___x_2271_);
        leanh::lean_ctor_set(v___x_2272_, 3, v___x_2253_);
        leanh::lean_inc_ref(v___x_2272_);
        v___x_2273_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2246_, v___x_2272_);
        v___x_2274_ = l_Lean_Syntax_node2(v___x_2240_, v___x_2248_, v___x_2249_, v___x_2273_);
        v___x_2275_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__69;
        v___x_2276_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__step__2___closed__70;
        v___x_2277_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2277_, 0, v___x_2240_);
        leanh::lean_ctor_set(v___x_2277_, 1, v___x_2275_);
        v___x_2278_ = l_Lean_Syntax_node2(v___x_2240_, v___x_2262_, v___x_2258_, v___x_2272_);
        v___x_2279_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2246_, v___x_2278_);
        v___x_2280_ = l_Lean_Syntax_node4(
            v___x_2240_,
            v___x_2276_,
            v___x_2277_,
            v___x_2279_,
            v___x_2258_,
            v___x_2258_,
        );
        v___x_2281_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__25;
        v___x_2282_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__26;
        v___x_2283_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2283_, 0, v___x_2240_);
        leanh::lean_ctor_set(v___x_2283_, 1, v___x_2281_);
        v___x_2284_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__28;
        v___x_2285_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2284_, v___x_2258_);
        v___x_2286_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__29;
        v___x_2287_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2287_, 0, v___x_2240_);
        leanh::lean_ctor_set(v___x_2287_, 1, v___x_2286_);
        v___x_2288_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2246_, v___x_2287_);
        v___x_2289_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__30;
        v___x_2290_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2290_, 0, v___x_2240_);
        leanh::lean_ctor_set(v___x_2290_, 1, v___x_2289_);
        v___x_2291_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__32;
        v___x_2292_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__58);
        v___x_2293_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__59;
        v___x_2294_ =
            l_Lean_addMacroScope(v_quotContext_2236_, v___x_2293_, v_currMacroScope_2237_);
        v___x_2295_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2295_, 0, v___x_2240_);
        leanh::lean_ctor_set(v___x_2295_, 1, v___x_2292_);
        leanh::lean_ctor_set(v___x_2295_, 2, v___x_2294_);
        leanh::lean_ctor_set(v___x_2295_, 3, v___x_2253_);
        v___x_2296_ = l_Lean_Syntax_node3(
            v___x_2240_,
            v___x_2291_,
            v___x_2258_,
            v___x_2258_,
            v___x_2295_,
        );
        v___x_2297_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__40;
        v___x_2298_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2298_, 0, v___x_2240_);
        leanh::lean_ctor_set(v___x_2298_, 1, v___x_2297_);
        v___x_2299_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61), core::ptr::addr_of_mut!(l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61_once), _init_l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__61);
        v___x_2300_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__62;
        v___x_2301_ =
            l_Lean_addMacroScope(v_quotContext_2236_, v___x_2300_, v_currMacroScope_2237_);
        v___x_2302_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2302_, 0, v___x_2240_);
        leanh::lean_ctor_set(v___x_2302_, 1, v___x_2299_);
        leanh::lean_ctor_set(v___x_2302_, 2, v___x_2301_);
        leanh::lean_ctor_set(v___x_2302_, 3, v___x_2253_);
        v___x_2303_ = l_Lean_Syntax_node3(
            v___x_2240_,
            v___x_2291_,
            v___x_2258_,
            v___x_2258_,
            v___x_2302_,
        );
        v___x_2304_ = l_Lean_Syntax_node3(
            v___x_2240_,
            v___x_2246_,
            v___x_2296_,
            v___x_2298_,
            v___x_2303_,
        );
        v___x_2305_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__63;
        v___x_2306_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2306_, 0, v___x_2240_);
        leanh::lean_ctor_set(v___x_2306_, 1, v___x_2305_);
        v___x_2307_ = l_Lean_Syntax_node3(
            v___x_2240_,
            v___x_2246_,
            v___x_2290_,
            v___x_2304_,
            v___x_2306_,
        );
        v___x_2308_ = l_Lean_Syntax_node6(
            v___x_2240_,
            v___x_2282_,
            v___x_2283_,
            v___x_2285_,
            v___x_2258_,
            v___x_2288_,
            v___x_2307_,
            v___x_2258_,
        );
        v___x_2309_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__4;
        v___x_2310_ = l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___closed__5;
        v___x_2311_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2311_, 0, v___x_2240_);
        leanh::lean_ctor_set(v___x_2311_, 1, v___x_2310_);
        v___x_2312_ = l_tacticDeriving__LawfulEq__tactic__step___closed__1;
        v___x_2313_ = l_tacticDeriving__LawfulEq__tactic__step___closed__2;
        v___x_2314_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2314_, 0, v___x_2240_);
        leanh::lean_ctor_set(v___x_2314_, 1, v___x_2313_);
        v___x_2315_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2312_, v___x_2314_);
        v___x_2316_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2246_, v___x_2315_);
        v___x_2317_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2245_, v___x_2316_);
        v___x_2318_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2244_, v___x_2317_);
        v___x_2319_ = l_Lean_Syntax_node2(v___x_2240_, v___x_2309_, v___x_2311_, v___x_2318_);
        v___x_2320_ = l_Lean_Syntax_node3(
            v___x_2240_,
            v___x_2246_,
            v___x_2308_,
            v___x_2258_,
            v___x_2319_,
        );
        v___x_2321_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2245_, v___x_2320_);
        v___x_2322_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2244_, v___x_2321_);
        leanh::lean_inc_ref(v___x_2268_);
        v___x_2323_ = l_Lean_Syntax_node2(v___x_2240_, v___x_2266_, v___x_2268_, v___x_2322_);
        v___x_2324_ = l_Lean_Syntax_node5(
            v___x_2240_,
            v___x_2246_,
            v___x_2274_,
            v___x_2258_,
            v___x_2280_,
            v___x_2258_,
            v___x_2323_,
        );
        v___x_2325_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2245_, v___x_2324_);
        v___x_2326_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2244_, v___x_2325_);
        v___x_2327_ = l_Lean_Syntax_node2(v___x_2240_, v___x_2266_, v___x_2268_, v___x_2326_);
        v___x_2328_ = l_Lean_Syntax_node5(
            v___x_2240_,
            v___x_2246_,
            v___x_2256_,
            v___x_2258_,
            v___x_2265_,
            v___x_2258_,
            v___x_2327_,
        );
        v___x_2329_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2245_, v___x_2328_);
        v___x_2330_ = l_Lean_Syntax_node1(v___x_2240_, v___x_2244_, v___x_2329_);
        v___x_2331_ = l_DerivingHelpers___aux__Init__LawfulBEqTactics______macroRules__DerivingHelpers__tacticDeriving__ReflEq__tactic__1___closed__64;
        v___x_2332_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2332_, 0, v___x_2240_);
        leanh::lean_ctor_set(v___x_2332_, 1, v___x_2331_);
        v___x_2333_ = l_Lean_Syntax_node3(
            v___x_2240_,
            v___x_2241_,
            v___x_2243_,
            v___x_2330_,
            v___x_2332_,
        );
        v___x_2334_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2334_, 0, v___x_2333_);
        leanh::lean_ctor_set(v___x_2334_, 1, v_a_2231_);
        return v___x_2334_;
    }
}
pub unsafe fn l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1___boxed(
    mut v_x_2335_: *mut leanh::LeanObject,
    mut v_a_2336_: *mut leanh::LeanObject,
    mut v_a_2337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2338_ =
        l___aux__Init__LawfulBEqTactics______macroRules__tacticDeriving__LawfulEq__tactic__1(
            v_x_2335_, v_a_2336_, v_a_2337_,
        );
    leanh::lean_dec_ref(v_a_2336_);
    return v_res_2338_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_LawfulBEqTactics(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Core(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_LawfulBEqTactics(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_LawfulBEqTactics(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Core(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_LawfulBEqTactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_LawfulBEqTactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_LawfulBEqTactics(builtin);
}