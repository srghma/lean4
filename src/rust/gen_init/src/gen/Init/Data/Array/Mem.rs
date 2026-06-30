// Lean compiler output
// Module: Init.Data.Array.Mem
// Imports: Init.Data.Array.Basic Init.WFTactics Init.Data.List.BasicAux Init.Data.Nat.Linear Init.MetaTypes
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::List::BasicAux::{
    initialize_Init_Data_List_BasicAux, runtime_initialize_Init_Data_List_BasicAux,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::MetaTypes::{initialize_Init_MetaTypes, runtime_initialize_Init_MetaTypes};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_node5,
    l_Lean_Syntax_node6, l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::WFTactics::{initialize_Init_WFTactics, runtime_initialize_Init_WFTactics};
pub static l_Array_tacticArray__get__dec___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [65, 114, 114, 97, 121, 0],
    };
static mut l_Array_tacticArray__get__dec___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_tacticArray__get__dec___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Array_tacticArray__get__dec___closed__1_value: leanh::LeanStringObject<20> =
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
            116, 97, 99, 116, 105, 99, 65, 114, 114, 97, 121, 95, 103, 101, 116, 95, 100, 101, 99,
            0,
        ],
    };
static mut l_Array_tacticArray__get__dec___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_tacticArray__get__dec___closed__1_value)
        as *mut leanh::LeanObject;
static l_Array_tacticArray__get__dec___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_tacticArray__get__dec___closed__0_value)
                as *mut leanh::LeanObject,
            8749134177695247953 as *mut leanh::LeanObject,
        ],
    };
pub static l_Array_tacticArray__get__dec___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_tacticArray__get__dec___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_tacticArray__get__dec___closed__1_value)
                as *mut leanh::LeanObject,
            8204503547653720067 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_tacticArray__get__dec___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_tacticArray__get__dec___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Array_tacticArray__get__dec___closed__3_value: leanh::LeanStringObject<14> =
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
            97, 114, 114, 97, 121, 95, 103, 101, 116, 95, 100, 101, 99, 0,
        ],
    };
static mut l_Array_tacticArray__get__dec___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_tacticArray__get__dec___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Array_tacticArray__get__dec___closed__4_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Array_tacticArray__get__dec___closed__3_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_tacticArray__get__dec___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_tacticArray__get__dec___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Array_tacticArray__get__dec___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_tacticArray__get__dec___closed__2_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_tacticArray__get__dec___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_tacticArray__get__dec___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_tacticArray__get__dec___closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Array_tacticArray__get__dec: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_tacticArray__get__dec___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__3_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 105, 114, 115, 116, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__3_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__3_value) as *mut leanh::LeanObject,12551601070224435259 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__5_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__5_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__7_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 111, 117, 112, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__7_value) as *mut leanh::LeanObject,2214559063752339918 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__9_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__10_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__10_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__10_value) as *mut leanh::LeanObject,8504843326314613972 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__12_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__12_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__12_value) as *mut leanh::LeanObject,17228437386856258271 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__14_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__14_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__15_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__15_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__15_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__15_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__15_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__15_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__14_value) as *mut leanh::LeanObject,8689124066155232629 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__15_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__16_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__16_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__17_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [119, 105, 116, 104, 82, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__17_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__17_value) as *mut leanh::LeanObject,6022092293134036165 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__19_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [119, 105, 116, 104, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__19_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__20_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 112, 112, 108, 121, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__20_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__20_value) as *mut leanh::LeanObject,5826123769708379594 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__22_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__22_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__23_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__23_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__22_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__23_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__25_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [78, 97, 116, 46, 108, 116, 95, 111, 102, 95, 108, 116, 95, 111, 102, 95, 108, 101, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__25_value) as *mut leanh::LeanObject;
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__27_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__27_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__28_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [108, 116, 95, 111, 102, 95, 108, 116, 95, 111, 102, 95, 108, 101, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__28_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__29_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__27_value) as *mut leanh::LeanObject,11442535297760353691 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__29_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__29_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__28_value) as *mut leanh::LeanObject,16353715261002541318 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__29_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__30_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__29_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__30_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__31_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__30_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__31_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__22_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__14_value) as *mut leanh::LeanObject,7932075773091973500 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__33_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__33: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__33_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__22_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__33_value) as *mut leanh::LeanObject,7306243862518720553 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__35_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__35: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__35_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__36_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__35_value) as *mut leanh::LeanObject,9871775667037945883 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__36: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__36_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__37_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__37: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__37_value) as *mut leanh::LeanObject;
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__39_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array_tacticArray__get__dec___closed__0_value) as *mut leanh::LeanObject,8749134177695247953 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__39: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__39_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__40_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__39_value) as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__40: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__40_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__41_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__40_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__41: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__41_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__42_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 105, 122, 101, 79, 102, 95, 103, 101, 116, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__42: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__42_value) as *mut leanh::LeanObject;
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__43_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__43: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__44_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__42_value) as *mut leanh::LeanObject,3219847148492649636 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__44: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__44_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__45_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array_tacticArray__get__dec___closed__0_value) as *mut leanh::LeanObject,8749134177695247953 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__45_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__45_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__42_value) as *mut leanh::LeanObject,16855211853546651350 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__45: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__45_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__46_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__45_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__46: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__46_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__47_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__46_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__47: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__47_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__48_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 108, 108, 105, 112, 115, 105, 115, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__48: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__48_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__49_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__49_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__49_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__49_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__49_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__22_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__49_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__49_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__48_value) as *mut leanh::LeanObject,15691513163239863397 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__49: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__49_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__50_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [46, 46, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__50: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__50_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__51_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__51: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__51_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__52_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__52: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__52_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__53_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__53: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__53_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__53_value) as *mut leanh::LeanObject,12783917532758215986 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__55_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__55: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__55_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__55_value) as *mut leanh::LeanObject,3488656302031949961 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__57_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__57: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__57_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__57_value) as *mut leanh::LeanObject,10138443044734372301 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__59_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 111, 115, 67, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__59: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__59_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__59_value) as *mut leanh::LeanObject,9555431800314169832 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__61_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [43, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__61: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__61_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__62_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 114, 105, 116, 104, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__62: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__62_value) as *mut leanh::LeanObject;
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__64_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__62_value) as *mut leanh::LeanObject,3738010876686032200 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__64: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__64_value) as *mut leanh::LeanObject;
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__66_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [115, 105, 122, 101, 79, 102, 95, 103, 101, 116, 69, 108, 101, 109, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__66: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__66_value) as *mut leanh::LeanObject;
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__67_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__67: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__68_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__66_value) as *mut leanh::LeanObject,13917302943916010233 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__68: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__68_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__69_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array_tacticArray__get__dec___closed__0_value) as *mut leanh::LeanObject,8749134177695247953 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__69_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__69_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__66_value) as *mut leanh::LeanObject,16263613932012225963 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__69: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__69_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__70_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__69_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__70: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__70_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__71_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__70_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__71: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__71_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [116, 97, 99, 116, 105, 99, 68, 101, 99, 114, 101, 97, 115, 105, 110, 103, 95, 116, 114, 105, 118, 105, 97, 108, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___closed__0_value) as *mut leanh::LeanObject,5744670087858236374 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Array_tacticArray__mem__dec___closed__0_value: leanh::LeanStringObject<20> =
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
            116, 97, 99, 116, 105, 99, 65, 114, 114, 97, 121, 95, 109, 101, 109, 95, 100, 101, 99,
            0,
        ],
    };
static mut l_Array_tacticArray__mem__dec___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_tacticArray__mem__dec___closed__0_value)
        as *mut leanh::LeanObject;
static l_Array_tacticArray__mem__dec___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_tacticArray__get__dec___closed__0_value)
                as *mut leanh::LeanObject,
            8749134177695247953 as *mut leanh::LeanObject,
        ],
    };
pub static l_Array_tacticArray__mem__dec___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_tacticArray__mem__dec___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_tacticArray__mem__dec___closed__0_value)
                as *mut leanh::LeanObject,
            701019970865544781 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_tacticArray__mem__dec___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_tacticArray__mem__dec___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Array_tacticArray__mem__dec___closed__2_value: leanh::LeanStringObject<14> =
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
            97, 114, 114, 97, 121, 95, 109, 101, 109, 95, 100, 101, 99, 0,
        ],
    };
static mut l_Array_tacticArray__mem__dec___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_tacticArray__mem__dec___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Array_tacticArray__mem__dec___closed__3_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Array_tacticArray__mem__dec___closed__2_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_tacticArray__mem__dec___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_tacticArray__mem__dec___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Array_tacticArray__mem__dec___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_tacticArray__mem__dec___closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_tacticArray__mem__dec___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_tacticArray__mem__dec___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_tacticArray__mem__dec___closed__4_value)
        as *mut leanh::LeanObject;
pub static mut l_Array_tacticArray__mem__dec: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_tacticArray__mem__dec___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__0_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 114, 114, 97, 121, 46, 115, 105, 122, 101, 79, 102, 95, 108, 116, 95, 111, 102, 95, 109, 101, 109, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__2_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 105, 122, 101, 79, 102, 95, 108, 116, 95, 111, 102, 95, 109, 101, 109, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__2_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array_tacticArray__get__dec___closed__0_value) as *mut leanh::LeanObject,8749134177695247953 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__2_value) as *mut leanh::LeanObject,4212709588772922524 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__3_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__6_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 115, 115, 117, 109, 112, 116, 105, 111, 110, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__6_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__7_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__7_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__7_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__7_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__6_value) as *mut leanh::LeanObject,16687334436616221424 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__8_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 111, 110, 101, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__8_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__9_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__9_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__9_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__9_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__8_value) as *mut leanh::LeanObject,8876691400619696497 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__10_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 121, 110, 116, 104, 101, 116, 105, 99, 72, 111, 108, 101, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__10_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__11_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__11_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__11_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__11_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__11_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__22_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__11_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__10_value) as *mut leanh::LeanObject,11921244625177918938 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__12_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [63, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__13_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__13_value) as *mut leanh::LeanObject;
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__13_value) as *mut leanh::LeanObject,8738205681931236784 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__15_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__16_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 97, 115, 101, 39, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__16_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__17_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__17_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__17_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__17_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__17_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__17_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__16_value) as *mut leanh::LeanObject,7640173075534255494 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__17_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__18_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 97, 115, 101, 65, 114, 103, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__18_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__19_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__19_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__19_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__19_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__19_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__19_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__19_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__18_value) as *mut leanh::LeanObject,14546932361418667927 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__19_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__20_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [98, 105, 110, 100, 101, 114, 73, 100, 101, 110, 116, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__20_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__21_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__21_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__21_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__20_value) as *mut leanh::LeanObject,13771926289831477797 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__21_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__22_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__22_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_614_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__25;
    v___x_615_ = l_String_toRawSubstring_x27(v___x_614_);
    return v___x_615_;
}
pub unsafe fn _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38()
-> *mut leanh::LeanObject {
    let mut v___x_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_642_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__37;
    v___x_643_ = l_String_toRawSubstring_x27(v___x_642_);
    return v___x_643_;
}
pub unsafe fn _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__43()
-> *mut leanh::LeanObject {
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_652_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__42;
    v___x_653_ = l_String_toRawSubstring_x27(v___x_652_);
    return v___x_653_;
}
pub unsafe fn _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63()
-> *mut leanh::LeanObject {
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_700_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__62;
    v___x_701_ = l_String_toRawSubstring_x27(v___x_700_);
    return v___x_701_;
}
pub unsafe fn _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65()
-> *mut leanh::LeanObject {
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_704_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_704_;
}
pub unsafe fn _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__67()
-> *mut leanh::LeanObject {
    let mut v___x_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_706_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__66;
    v___x_707_ = l_String_toRawSubstring_x27(v___x_706_);
    return v___x_707_;
}
pub unsafe fn l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1(
    mut v_x_719_: *mut leanh::LeanObject,
    mut v_a_720_: *mut leanh::LeanObject,
    mut v_a_721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: u8 = 0;
    v___x_722_ = l_Array_tacticArray__get__dec___closed__2;
    v___x_723_ = l_Lean_Syntax_isOfKind(v_x_719_, v___x_722_);
    if v___x_723_ == 0 {
        let mut v___x_724_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_725_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_724_ = leanh::lean_box(1);
        v___x_725_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_725_, 0, v___x_724_);
        leanh::lean_ctor_set(v___x_725_, 1, v_a_721_);
        return v___x_725_;
    } else {
        let mut v_quotContext_726_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_727_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_728_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_729_: u8 = 0;
        let mut v___x_730_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_731_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_740_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_750_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_751_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_753_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_754_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_757_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_760_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_769_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_772_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_773_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_776_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_779_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_782_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_783_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_784_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_785_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_786_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_790_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_791_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_794_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_795_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_799_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_801_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_802_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_803_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_806_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_807_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_808_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_809_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_810_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_811_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_812_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_813_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_814_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_815_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_816_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_817_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_822_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_825_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_837_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_726_ = leanh::lean_ctor_get(v_a_720_, 1);
        v_currMacroScope_727_ = leanh::lean_ctor_get(v_a_720_, 2);
        v_ref_728_ = leanh::lean_ctor_get(v_a_720_, 5);
        v___x_729_ = 0;
        v___x_730_ = l_Lean_SourceInfo_fromRef(v_ref_728_, v___x_729_);
        v___x_731_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__3;
        v___x_732_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4;
        leanh::lean_inc_n(v___x_730_, 60);
        v___x_733_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_733_, 0, v___x_730_);
        leanh::lean_ctor_set(v___x_733_, 1, v___x_731_);
        v___x_734_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__6;
        v___x_735_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__8;
        v___x_736_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__9;
        v___x_737_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_737_, 0, v___x_730_);
        leanh::lean_ctor_set(v___x_737_, 1, v___x_736_);
        v___x_738_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11;
        v___x_739_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13;
        v___x_740_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__15;
        v___x_741_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__16;
        v___x_742_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_742_, 0, v___x_730_);
        leanh::lean_ctor_set(v___x_742_, 1, v___x_741_);
        v___x_743_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18;
        v___x_744_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__19;
        v___x_745_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_745_, 0, v___x_730_);
        leanh::lean_ctor_set(v___x_745_, 1, v___x_744_);
        v___x_746_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__20;
        v___x_747_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21;
        v___x_748_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_748_, 0, v___x_730_);
        leanh::lean_ctor_set(v___x_748_, 1, v___x_746_);
        v___x_749_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24;
        v___x_750_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26_once), _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26);
        v___x_751_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__29;
        leanh::lean_inc_n(v_currMacroScope_727_, 5);
        leanh::lean_inc_n(v_quotContext_726_, 5);
        v___x_752_ = l_Lean_addMacroScope(v_quotContext_726_, v___x_751_, v_currMacroScope_727_);
        v___x_753_ = leanh::lean_box(0);
        v___x_754_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__31;
        v___x_755_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_755_, 0, v___x_730_);
        leanh::lean_ctor_set(v___x_755_, 1, v___x_750_);
        leanh::lean_ctor_set(v___x_755_, 2, v___x_752_);
        leanh::lean_ctor_set(v___x_755_, 3, v___x_754_);
        v___x_756_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32;
        v___x_757_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34;
        v___x_758_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__36;
        v___x_759_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38_once), _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38);
        v___x_760_ = leanh::lean_box(0);
        v___x_761_ = l_Lean_addMacroScope(v_quotContext_726_, v___x_760_, v_currMacroScope_727_);
        v___x_762_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__41;
        v___x_763_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_763_, 0, v___x_730_);
        leanh::lean_ctor_set(v___x_763_, 1, v___x_759_);
        leanh::lean_ctor_set(v___x_763_, 2, v___x_761_);
        leanh::lean_ctor_set(v___x_763_, 3, v___x_762_);
        v___x_764_ = l_Lean_Syntax_node1(v___x_730_, v___x_758_, v___x_763_);
        leanh::lean_inc_ref_n(v___x_742_, 2);
        v___x_765_ = l_Lean_Syntax_node2(v___x_730_, v___x_757_, v___x_742_, v___x_764_);
        v___x_766_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__43), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__43_once), _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__43);
        v___x_767_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__44;
        v___x_768_ = l_Lean_addMacroScope(v_quotContext_726_, v___x_767_, v_currMacroScope_727_);
        v___x_769_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__47;
        v___x_770_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_770_, 0, v___x_730_);
        leanh::lean_ctor_set(v___x_770_, 1, v___x_766_);
        leanh::lean_ctor_set(v___x_770_, 2, v___x_768_);
        leanh::lean_ctor_set(v___x_770_, 3, v___x_769_);
        v___x_771_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__49;
        v___x_772_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__50;
        v___x_773_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_773_, 0, v___x_730_);
        leanh::lean_ctor_set(v___x_773_, 1, v___x_772_);
        v___x_774_ = l_Lean_Syntax_node1(v___x_730_, v___x_771_, v___x_773_);
        v___x_775_ = l_Lean_Syntax_node1(v___x_730_, v___x_734_, v___x_774_);
        leanh::lean_inc(v___x_775_);
        v___x_776_ = l_Lean_Syntax_node2(v___x_730_, v___x_749_, v___x_770_, v___x_775_);
        v___x_777_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__51;
        v___x_778_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_778_, 0, v___x_730_);
        leanh::lean_ctor_set(v___x_778_, 1, v___x_777_);
        leanh::lean_inc_ref_n(v___x_778_, 3);
        leanh::lean_inc(v___x_765_);
        v___x_779_ =
            l_Lean_Syntax_node3(v___x_730_, v___x_756_, v___x_765_, v___x_776_, v___x_778_);
        v___x_780_ = l_Lean_Syntax_node1(v___x_730_, v___x_734_, v___x_779_);
        leanh::lean_inc_ref(v___x_755_);
        v___x_781_ = l_Lean_Syntax_node2(v___x_730_, v___x_749_, v___x_755_, v___x_780_);
        leanh::lean_inc_ref(v___x_748_);
        v___x_782_ = l_Lean_Syntax_node2(v___x_730_, v___x_747_, v___x_748_, v___x_781_);
        v___x_783_ = l_Lean_Syntax_node1(v___x_730_, v___x_734_, v___x_782_);
        v___x_784_ = l_Lean_Syntax_node1(v___x_730_, v___x_739_, v___x_783_);
        v___x_785_ = l_Lean_Syntax_node1(v___x_730_, v___x_738_, v___x_784_);
        leanh::lean_inc_ref(v___x_745_);
        v___x_786_ = l_Lean_Syntax_node2(v___x_730_, v___x_743_, v___x_745_, v___x_785_);
        v___x_787_ = l_Lean_Syntax_node1(v___x_730_, v___x_734_, v___x_786_);
        v___x_788_ = l_Lean_Syntax_node1(v___x_730_, v___x_739_, v___x_787_);
        v___x_789_ = l_Lean_Syntax_node1(v___x_730_, v___x_738_, v___x_788_);
        v___x_790_ =
            l_Lean_Syntax_node3(v___x_730_, v___x_740_, v___x_742_, v___x_789_, v___x_778_);
        v___x_791_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__52;
        v___x_792_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_792_, 0, v___x_730_);
        leanh::lean_ctor_set(v___x_792_, 1, v___x_791_);
        v___x_793_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__53;
        v___x_794_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54;
        v___x_795_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_795_, 0, v___x_730_);
        leanh::lean_ctor_set(v___x_795_, 1, v___x_793_);
        v___x_796_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56;
        v___x_797_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58;
        v___x_798_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60;
        v___x_799_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__61;
        v___x_800_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_800_, 0, v___x_730_);
        leanh::lean_ctor_set(v___x_800_, 1, v___x_799_);
        v___x_801_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63_once), _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63);
        v___x_802_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__64;
        v___x_803_ = l_Lean_addMacroScope(v_quotContext_726_, v___x_802_, v_currMacroScope_727_);
        v___x_804_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_804_, 0, v___x_730_);
        leanh::lean_ctor_set(v___x_804_, 1, v___x_801_);
        leanh::lean_ctor_set(v___x_804_, 2, v___x_803_);
        leanh::lean_ctor_set(v___x_804_, 3, v___x_753_);
        v___x_805_ = l_Lean_Syntax_node2(v___x_730_, v___x_798_, v___x_800_, v___x_804_);
        v___x_806_ = l_Lean_Syntax_node1(v___x_730_, v___x_797_, v___x_805_);
        v___x_807_ = l_Lean_Syntax_node1(v___x_730_, v___x_734_, v___x_806_);
        v___x_808_ = l_Lean_Syntax_node1(v___x_730_, v___x_796_, v___x_807_);
        v___x_809_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65_once), _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65);
        v___x_810_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_810_, 0, v___x_730_);
        leanh::lean_ctor_set(v___x_810_, 1, v___x_734_);
        leanh::lean_ctor_set(v___x_810_, 2, v___x_809_);
        leanh::lean_inc_ref_n(v___x_810_, 3);
        v___x_811_ = l_Lean_Syntax_node6(
            v___x_730_, v___x_794_, v___x_795_, v___x_808_, v___x_810_, v___x_810_, v___x_810_,
            v___x_810_,
        );
        leanh::lean_inc(v___x_811_);
        leanh::lean_inc_ref(v___x_792_);
        v___x_812_ =
            l_Lean_Syntax_node3(v___x_730_, v___x_734_, v___x_790_, v___x_792_, v___x_811_);
        v___x_813_ = l_Lean_Syntax_node1(v___x_730_, v___x_739_, v___x_812_);
        v___x_814_ = l_Lean_Syntax_node1(v___x_730_, v___x_738_, v___x_813_);
        leanh::lean_inc_ref(v___x_737_);
        v___x_815_ = l_Lean_Syntax_node2(v___x_730_, v___x_735_, v___x_737_, v___x_814_);
        v___x_816_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__67), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__67_once), _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__67);
        v___x_817_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__68;
        v___x_818_ = l_Lean_addMacroScope(v_quotContext_726_, v___x_817_, v_currMacroScope_727_);
        v___x_819_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__71;
        v___x_820_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_820_, 0, v___x_730_);
        leanh::lean_ctor_set(v___x_820_, 1, v___x_816_);
        leanh::lean_ctor_set(v___x_820_, 2, v___x_818_);
        leanh::lean_ctor_set(v___x_820_, 3, v___x_819_);
        v___x_821_ = l_Lean_Syntax_node2(v___x_730_, v___x_749_, v___x_820_, v___x_775_);
        v___x_822_ =
            l_Lean_Syntax_node3(v___x_730_, v___x_756_, v___x_765_, v___x_821_, v___x_778_);
        v___x_823_ = l_Lean_Syntax_node1(v___x_730_, v___x_734_, v___x_822_);
        v___x_824_ = l_Lean_Syntax_node2(v___x_730_, v___x_749_, v___x_755_, v___x_823_);
        v___x_825_ = l_Lean_Syntax_node2(v___x_730_, v___x_747_, v___x_748_, v___x_824_);
        v___x_826_ = l_Lean_Syntax_node1(v___x_730_, v___x_734_, v___x_825_);
        v___x_827_ = l_Lean_Syntax_node1(v___x_730_, v___x_739_, v___x_826_);
        v___x_828_ = l_Lean_Syntax_node1(v___x_730_, v___x_738_, v___x_827_);
        v___x_829_ = l_Lean_Syntax_node2(v___x_730_, v___x_743_, v___x_745_, v___x_828_);
        v___x_830_ = l_Lean_Syntax_node1(v___x_730_, v___x_734_, v___x_829_);
        v___x_831_ = l_Lean_Syntax_node1(v___x_730_, v___x_739_, v___x_830_);
        v___x_832_ = l_Lean_Syntax_node1(v___x_730_, v___x_738_, v___x_831_);
        v___x_833_ =
            l_Lean_Syntax_node3(v___x_730_, v___x_740_, v___x_742_, v___x_832_, v___x_778_);
        v___x_834_ =
            l_Lean_Syntax_node3(v___x_730_, v___x_734_, v___x_833_, v___x_792_, v___x_811_);
        v___x_835_ = l_Lean_Syntax_node1(v___x_730_, v___x_739_, v___x_834_);
        v___x_836_ = l_Lean_Syntax_node1(v___x_730_, v___x_738_, v___x_835_);
        v___x_837_ = l_Lean_Syntax_node2(v___x_730_, v___x_735_, v___x_737_, v___x_836_);
        v___x_838_ = l_Lean_Syntax_node2(v___x_730_, v___x_734_, v___x_815_, v___x_837_);
        v___x_839_ = l_Lean_Syntax_node2(v___x_730_, v___x_732_, v___x_733_, v___x_838_);
        v___x_840_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_840_, 0, v___x_839_);
        leanh::lean_ctor_set(v___x_840_, 1, v_a_721_);
        return v___x_840_;
    }
}
pub unsafe fn l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___boxed(
    mut v_x_841_: *mut leanh::LeanObject,
    mut v_a_842_: *mut leanh::LeanObject,
    mut v_a_843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_844_ =
        l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1(
            v_x_841_, v_a_842_, v_a_843_,
        );
    leanh::lean_dec_ref(v_a_842_);
    return v_res_844_;
}
pub unsafe fn l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1(
    mut v_x_848_: *mut leanh::LeanObject,
    mut v_a_849_: *mut leanh::LeanObject,
    mut v_a_850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: u8 = 0;
    v___x_851_ = l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___closed__1;
    v___x_852_ = l_Lean_Syntax_isOfKind(v_x_848_, v___x_851_);
    if v___x_852_ == 0 {
        let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_853_ = leanh::lean_box(1);
        v___x_854_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_854_, 0, v___x_853_);
        leanh::lean_ctor_set(v___x_854_, 1, v_a_850_);
        return v___x_854_;
    } else {
        let mut v_ref_855_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_856_: u8 = 0;
        let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ref_855_ = leanh::lean_ctor_get(v_a_849_, 5);
        v___x_856_ = 0;
        v___x_857_ = l_Lean_SourceInfo_fromRef(v_ref_855_, v___x_856_);
        v___x_858_ = l_Array_tacticArray__get__dec___closed__2;
        v___x_859_ = l_Array_tacticArray__get__dec___closed__3;
        leanh::lean_inc(v___x_857_);
        v___x_860_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_860_, 0, v___x_857_);
        leanh::lean_ctor_set(v___x_860_, 1, v___x_859_);
        v___x_861_ = l_Lean_Syntax_node1(v___x_857_, v___x_858_, v___x_860_);
        v___x_862_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_862_, 0, v___x_861_);
        leanh::lean_ctor_set(v___x_862_, 1, v_a_850_);
        return v___x_862_;
    }
}
pub unsafe fn l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___boxed(
    mut v_x_863_: *mut leanh::LeanObject,
    mut v_a_864_: *mut leanh::LeanObject,
    mut v_a_865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_866_ =
        l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1(
            v_x_863_, v_a_864_, v_a_865_,
        );
    leanh::lean_dec_ref(v_a_864_);
    return v_res_866_;
}
pub unsafe fn _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_881_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__0;
    v___x_882_ = l_String_toRawSubstring_x27(v___x_881_);
    return v___x_882_;
}
pub unsafe fn _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_913_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__13;
    v___x_914_ = l_String_toRawSubstring_x27(v___x_913_);
    return v___x_914_;
}
pub unsafe fn l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1(
    mut v_x_934_: *mut leanh::LeanObject,
    mut v_a_935_: *mut leanh::LeanObject,
    mut v_a_936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: u8 = 0;
    v___x_937_ = l_Array_tacticArray__mem__dec___closed__1;
    v___x_938_ = l_Lean_Syntax_isOfKind(v_x_934_, v___x_937_);
    if v___x_938_ == 0 {
        let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_939_ = leanh::lean_box(1);
        v___x_940_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_940_, 0, v___x_939_);
        leanh::lean_ctor_set(v___x_940_, 1, v_a_936_);
        return v___x_940_;
    } else {
        let mut v_quotContext_941_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_942_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_943_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_944_: u8 = 0;
        let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_946_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_955_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_962_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_965_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_966_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_971_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_941_ = leanh::lean_ctor_get(v_a_935_, 1);
        v_currMacroScope_942_ = leanh::lean_ctor_get(v_a_935_, 2);
        v_ref_943_ = leanh::lean_ctor_get(v_a_935_, 5);
        v___x_944_ = 0;
        v___x_945_ = l_Lean_SourceInfo_fromRef(v_ref_943_, v___x_944_);
        v___x_946_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__3;
        v___x_947_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4;
        leanh::lean_inc_n(v___x_945_, 61);
        v___x_948_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_948_, 0, v___x_945_);
        leanh::lean_ctor_set(v___x_948_, 1, v___x_946_);
        v___x_949_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__6;
        v___x_950_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__8;
        v___x_951_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__9;
        v___x_952_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_952_, 0, v___x_945_);
        leanh::lean_ctor_set(v___x_952_, 1, v___x_951_);
        v___x_953_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11;
        v___x_954_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13;
        v___x_955_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18;
        v___x_956_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__19;
        v___x_957_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_957_, 0, v___x_945_);
        leanh::lean_ctor_set(v___x_957_, 1, v___x_956_);
        v___x_958_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__20;
        v___x_959_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21;
        v___x_960_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_960_, 0, v___x_945_);
        leanh::lean_ctor_set(v___x_960_, 1, v___x_958_);
        v___x_961_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__1), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__1_once), _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__1);
        v___x_962_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__3;
        leanh::lean_inc_n(v_currMacroScope_942_, 5);
        leanh::lean_inc_n(v_quotContext_941_, 5);
        v___x_963_ = l_Lean_addMacroScope(v_quotContext_941_, v___x_962_, v_currMacroScope_942_);
        v___x_964_ = leanh::lean_box(0);
        v___x_965_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__5;
        v___x_966_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_966_, 0, v___x_945_);
        leanh::lean_ctor_set(v___x_966_, 1, v___x_961_);
        leanh::lean_ctor_set(v___x_966_, 2, v___x_963_);
        leanh::lean_ctor_set(v___x_966_, 3, v___x_965_);
        leanh::lean_inc_ref(v___x_966_);
        leanh::lean_inc_ref(v___x_960_);
        v___x_967_ = l_Lean_Syntax_node2(v___x_945_, v___x_959_, v___x_960_, v___x_966_);
        v___x_968_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__52;
        v___x_969_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_969_, 0, v___x_945_);
        leanh::lean_ctor_set(v___x_969_, 1, v___x_968_);
        v___x_970_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__6;
        v___x_971_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__7;
        v___x_972_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_972_, 0, v___x_945_);
        leanh::lean_ctor_set(v___x_972_, 1, v___x_970_);
        v___x_973_ = l_Lean_Syntax_node1(v___x_945_, v___x_971_, v___x_972_);
        v___x_974_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__8;
        v___x_975_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__9;
        v___x_976_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_976_, 0, v___x_945_);
        leanh::lean_ctor_set(v___x_976_, 1, v___x_974_);
        v___x_977_ = l_Lean_Syntax_node1(v___x_945_, v___x_975_, v___x_976_);
        leanh::lean_inc(v___x_973_);
        leanh::lean_inc_ref(v___x_969_);
        v___x_978_ = l_Lean_Syntax_node5(
            v___x_945_, v___x_949_, v___x_967_, v___x_969_, v___x_973_, v___x_969_, v___x_977_,
        );
        v___x_979_ = l_Lean_Syntax_node1(v___x_945_, v___x_954_, v___x_978_);
        v___x_980_ = l_Lean_Syntax_node1(v___x_945_, v___x_953_, v___x_979_);
        leanh::lean_inc_ref(v___x_957_);
        v___x_981_ = l_Lean_Syntax_node2(v___x_945_, v___x_955_, v___x_957_, v___x_980_);
        v___x_982_ = l_Lean_Syntax_node1(v___x_945_, v___x_949_, v___x_981_);
        v___x_983_ = l_Lean_Syntax_node1(v___x_945_, v___x_954_, v___x_982_);
        v___x_984_ = l_Lean_Syntax_node1(v___x_945_, v___x_953_, v___x_983_);
        leanh::lean_inc_ref(v___x_952_);
        v___x_985_ = l_Lean_Syntax_node2(v___x_945_, v___x_950_, v___x_952_, v___x_984_);
        v___x_986_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24;
        v___x_987_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26_once), _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26);
        v___x_988_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__29;
        v___x_989_ = l_Lean_addMacroScope(v_quotContext_941_, v___x_988_, v_currMacroScope_942_);
        v___x_990_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__31;
        v___x_991_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_991_, 0, v___x_945_);
        leanh::lean_ctor_set(v___x_991_, 1, v___x_987_);
        leanh::lean_ctor_set(v___x_991_, 2, v___x_989_);
        leanh::lean_ctor_set(v___x_991_, 3, v___x_990_);
        v___x_992_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32;
        v___x_993_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34;
        v___x_994_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__16;
        v___x_995_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_995_, 0, v___x_945_);
        leanh::lean_ctor_set(v___x_995_, 1, v___x_994_);
        v___x_996_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__36;
        v___x_997_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38_once), _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38);
        v___x_998_ = leanh::lean_box(0);
        v___x_999_ = l_Lean_addMacroScope(v_quotContext_941_, v___x_998_, v_currMacroScope_942_);
        v___x_1000_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__41;
        v___x_1001_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1001_, 0, v___x_945_);
        leanh::lean_ctor_set(v___x_1001_, 1, v___x_997_);
        leanh::lean_ctor_set(v___x_1001_, 2, v___x_999_);
        leanh::lean_ctor_set(v___x_1001_, 3, v___x_1000_);
        v___x_1002_ = l_Lean_Syntax_node1(v___x_945_, v___x_996_, v___x_1001_);
        v___x_1003_ = l_Lean_Syntax_node2(v___x_945_, v___x_993_, v___x_995_, v___x_1002_);
        v___x_1004_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__11;
        v___x_1005_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__12;
        v___x_1006_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1006_, 0, v___x_945_);
        leanh::lean_ctor_set(v___x_1006_, 1, v___x_1005_);
        v___x_1007_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__14), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__14_once), _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__14);
        v___x_1008_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__15;
        v___x_1009_ = l_Lean_addMacroScope(v_quotContext_941_, v___x_1008_, v_currMacroScope_942_);
        v___x_1010_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1010_, 0, v___x_945_);
        leanh::lean_ctor_set(v___x_1010_, 1, v___x_1007_);
        leanh::lean_ctor_set(v___x_1010_, 2, v___x_1009_);
        leanh::lean_ctor_set(v___x_1010_, 3, v___x_964_);
        leanh::lean_inc_ref(v___x_1010_);
        v___x_1011_ = l_Lean_Syntax_node2(v___x_945_, v___x_1004_, v___x_1006_, v___x_1010_);
        v___x_1012_ = l_Lean_Syntax_node1(v___x_945_, v___x_949_, v___x_1011_);
        v___x_1013_ = l_Lean_Syntax_node2(v___x_945_, v___x_986_, v___x_966_, v___x_1012_);
        v___x_1014_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__51;
        v___x_1015_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1015_, 0, v___x_945_);
        leanh::lean_ctor_set(v___x_1015_, 1, v___x_1014_);
        v___x_1016_ = l_Lean_Syntax_node3(
            v___x_945_,
            v___x_992_,
            v___x_1003_,
            v___x_1013_,
            v___x_1015_,
        );
        v___x_1017_ = l_Lean_Syntax_node1(v___x_945_, v___x_949_, v___x_1016_);
        v___x_1018_ = l_Lean_Syntax_node2(v___x_945_, v___x_986_, v___x_991_, v___x_1017_);
        v___x_1019_ = l_Lean_Syntax_node2(v___x_945_, v___x_959_, v___x_960_, v___x_1018_);
        v___x_1020_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65_once), _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65);
        v___x_1021_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_1021_, 0, v___x_945_);
        leanh::lean_ctor_set(v___x_1021_, 1, v___x_949_);
        leanh::lean_ctor_set(v___x_1021_, 2, v___x_1020_);
        v___x_1022_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__16;
        v___x_1023_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__17;
        v___x_1024_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1024_, 0, v___x_945_);
        leanh::lean_ctor_set(v___x_1024_, 1, v___x_1022_);
        v___x_1025_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__19;
        v___x_1026_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__21;
        v___x_1027_ = l_Lean_Syntax_node1(v___x_945_, v___x_1026_, v___x_1010_);
        leanh::lean_inc_ref_n(v___x_1021_, 6);
        v___x_1028_ = l_Lean_Syntax_node2(v___x_945_, v___x_1025_, v___x_1027_, v___x_1021_);
        v___x_1029_ = l_Lean_Syntax_node1(v___x_945_, v___x_949_, v___x_1028_);
        v___x_1030_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__22;
        v___x_1031_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1031_, 0, v___x_945_);
        leanh::lean_ctor_set(v___x_1031_, 1, v___x_1030_);
        v___x_1032_ = l_Lean_Syntax_node1(v___x_945_, v___x_949_, v___x_973_);
        v___x_1033_ = l_Lean_Syntax_node1(v___x_945_, v___x_954_, v___x_1032_);
        v___x_1034_ = l_Lean_Syntax_node1(v___x_945_, v___x_953_, v___x_1033_);
        v___x_1035_ = l_Lean_Syntax_node4(
            v___x_945_,
            v___x_1023_,
            v___x_1024_,
            v___x_1029_,
            v___x_1031_,
            v___x_1034_,
        );
        v___x_1036_ = l_Lean_Syntax_node3(
            v___x_945_,
            v___x_949_,
            v___x_1019_,
            v___x_1021_,
            v___x_1035_,
        );
        v___x_1037_ = l_Lean_Syntax_node1(v___x_945_, v___x_954_, v___x_1036_);
        v___x_1038_ = l_Lean_Syntax_node1(v___x_945_, v___x_953_, v___x_1037_);
        v___x_1039_ = l_Lean_Syntax_node2(v___x_945_, v___x_955_, v___x_957_, v___x_1038_);
        v___x_1040_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__53;
        v___x_1041_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54;
        v___x_1042_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1042_, 0, v___x_945_);
        leanh::lean_ctor_set(v___x_1042_, 1, v___x_1040_);
        v___x_1043_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56;
        v___x_1044_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58;
        v___x_1045_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60;
        v___x_1046_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__61;
        v___x_1047_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1047_, 0, v___x_945_);
        leanh::lean_ctor_set(v___x_1047_, 1, v___x_1046_);
        v___x_1048_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63_once), _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63);
        v___x_1049_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__64;
        v___x_1050_ = l_Lean_addMacroScope(v_quotContext_941_, v___x_1049_, v_currMacroScope_942_);
        v___x_1051_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1051_, 0, v___x_945_);
        leanh::lean_ctor_set(v___x_1051_, 1, v___x_1048_);
        leanh::lean_ctor_set(v___x_1051_, 2, v___x_1050_);
        leanh::lean_ctor_set(v___x_1051_, 3, v___x_964_);
        v___x_1052_ = l_Lean_Syntax_node2(v___x_945_, v___x_1045_, v___x_1047_, v___x_1051_);
        v___x_1053_ = l_Lean_Syntax_node1(v___x_945_, v___x_1044_, v___x_1052_);
        v___x_1054_ = l_Lean_Syntax_node1(v___x_945_, v___x_949_, v___x_1053_);
        v___x_1055_ = l_Lean_Syntax_node1(v___x_945_, v___x_1043_, v___x_1054_);
        v___x_1056_ = l_Lean_Syntax_node6(
            v___x_945_,
            v___x_1041_,
            v___x_1042_,
            v___x_1055_,
            v___x_1021_,
            v___x_1021_,
            v___x_1021_,
            v___x_1021_,
        );
        v___x_1057_ = l_Lean_Syntax_node3(
            v___x_945_,
            v___x_949_,
            v___x_1039_,
            v___x_1021_,
            v___x_1056_,
        );
        v___x_1058_ = l_Lean_Syntax_node1(v___x_945_, v___x_954_, v___x_1057_);
        v___x_1059_ = l_Lean_Syntax_node1(v___x_945_, v___x_953_, v___x_1058_);
        v___x_1060_ = l_Lean_Syntax_node2(v___x_945_, v___x_950_, v___x_952_, v___x_1059_);
        v___x_1061_ = l_Lean_Syntax_node2(v___x_945_, v___x_949_, v___x_985_, v___x_1060_);
        v___x_1062_ = l_Lean_Syntax_node2(v___x_945_, v___x_947_, v___x_948_, v___x_1061_);
        v___x_1063_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1063_, 0, v___x_1062_);
        leanh::lean_ctor_set(v___x_1063_, 1, v_a_936_);
        return v___x_1063_;
    }
}
pub unsafe fn l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___boxed(
    mut v_x_1064_: *mut leanh::LeanObject,
    mut v_a_1065_: *mut leanh::LeanObject,
    mut v_a_1066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1067_ =
        l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1(
            v_x_1064_, v_a_1065_, v_a_1066_,
        );
    leanh::lean_dec_ref(v_a_1065_);
    return v_res_1067_;
}
pub unsafe fn l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__2(
    mut v_x_1068_: *mut leanh::LeanObject,
    mut v_a_1069_: *mut leanh::LeanObject,
    mut v_a_1070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: u8 = 0;
    v___x_1071_ = l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___closed__1;
    v___x_1072_ = l_Lean_Syntax_isOfKind(v_x_1068_, v___x_1071_);
    if v___x_1072_ == 0 {
        let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1073_ = leanh::lean_box(1);
        v___x_1074_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1074_, 0, v___x_1073_);
        leanh::lean_ctor_set(v___x_1074_, 1, v_a_1070_);
        return v___x_1074_;
    } else {
        let mut v_ref_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1076_: u8 = 0;
        let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ref_1075_ = leanh::lean_ctor_get(v_a_1069_, 5);
        v___x_1076_ = 0;
        v___x_1077_ = l_Lean_SourceInfo_fromRef(v_ref_1075_, v___x_1076_);
        v___x_1078_ = l_Array_tacticArray__mem__dec___closed__1;
        v___x_1079_ = l_Array_tacticArray__mem__dec___closed__2;
        leanh::lean_inc(v___x_1077_);
        v___x_1080_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1080_, 0, v___x_1077_);
        leanh::lean_ctor_set(v___x_1080_, 1, v___x_1079_);
        v___x_1081_ = l_Lean_Syntax_node1(v___x_1077_, v___x_1078_, v___x_1080_);
        v___x_1082_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1082_, 0, v___x_1081_);
        leanh::lean_ctor_set(v___x_1082_, 1, v_a_1070_);
        return v___x_1082_;
    }
}
pub unsafe fn l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__2___boxed(
    mut v_x_1083_: *mut leanh::LeanObject,
    mut v_a_1084_: *mut leanh::LeanObject,
    mut v_a_1085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1086_ =
        l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__2(
            v_x_1083_, v_a_1084_, v_a_1085_,
        );
    leanh::lean_dec_ref(v_a_1084_);
    return v_res_1086_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Mem(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_BasicAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Mem(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_MetaTypes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Mem(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_BasicAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_MetaTypes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Mem(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Mem(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_Mem(builtin);
}