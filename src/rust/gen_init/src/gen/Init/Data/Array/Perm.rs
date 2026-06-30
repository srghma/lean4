// Lean compiler output
// Module: Init.Data.Array.Perm
// Imports: Init.Data.Array.Basic Init.Data.Array.Basic Init.Data.Array.Lemmas Init.Data.List.Nat.Perm Init.Data.List.Nat.TakeDrop Init.Data.List.Perm Init.Omega
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::List::Nat::Perm::{
    initialize_Init_Data_List_Nat_Perm, runtime_initialize_Init_Data_List_Nat_Perm,
};
use crate::r#gen::Init::Data::List::Nat::TakeDrop::{
    initialize_Init_Data_List_Nat_TakeDrop, runtime_initialize_Init_Data_List_Nat_TakeDrop,
};
use crate::r#gen::Init::Data::List::Perm::{
    initialize_Init_Data_List_Perm, runtime_initialize_Init_Data_List_Perm,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_addMacroScope,
    l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
pub static l_Array_term___x7e___00__closed__0_value: leanh::LeanStringObject<6> =
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
static mut l_Array_term___x7e___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term___x7e___00__closed__0_value) as *mut leanh::LeanObject;
pub static l_Array_term___x7e___00__closed__1_value: leanh::LeanStringObject<8> =
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
        m_data: [116, 101, 114, 109, 95, 126, 95, 0],
    };
static mut l_Array_term___x7e___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term___x7e___00__closed__1_value) as *mut leanh::LeanObject;
static l_Array_term___x7e___00__closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_term___x7e___00__closed__0_value)
                as *mut leanh::LeanObject,
            8749134177695247953 as *mut leanh::LeanObject,
        ],
    };
pub static l_Array_term___x7e___00__closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_term___x7e___00__closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term___x7e___00__closed__1_value)
                as *mut leanh::LeanObject,
            10991789070065804988 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term___x7e___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term___x7e___00__closed__2_value) as *mut leanh::LeanObject;
pub static l_Array_term___x7e___00__closed__3_value: leanh::LeanStringObject<8> =
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
static mut l_Array_term___x7e___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term___x7e___00__closed__3_value) as *mut leanh::LeanObject;
pub static l_Array_term___x7e___00__closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_term___x7e___00__closed__3_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term___x7e___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term___x7e___00__closed__4_value) as *mut leanh::LeanObject;
pub static l_Array_term___x7e___00__closed__5_value: leanh::LeanStringObject<4> =
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
        m_data: [32, 126, 32, 0],
    };
static mut l_Array_term___x7e___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term___x7e___00__closed__5_value) as *mut leanh::LeanObject;
pub static l_Array_term___x7e___00__closed__6_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Array_term___x7e___00__closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term___x7e___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term___x7e___00__closed__6_value) as *mut leanh::LeanObject;
pub static l_Array_term___x7e___00__closed__7_value: leanh::LeanStringObject<5> =
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
static mut l_Array_term___x7e___00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term___x7e___00__closed__7_value) as *mut leanh::LeanObject;
pub static l_Array_term___x7e___00__closed__8_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_term___x7e___00__closed__7_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term___x7e___00__closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term___x7e___00__closed__8_value) as *mut leanh::LeanObject;
pub static l_Array_term___x7e___00__closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Array_term___x7e___00__closed__8_value)
                as *mut leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term___x7e___00__closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term___x7e___00__closed__9_value) as *mut leanh::LeanObject;
pub static l_Array_term___x7e___00__closed__10_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_term___x7e___00__closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term___x7e___00__closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term___x7e___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term___x7e___00__closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term___x7e___00__closed__10_value) as *mut leanh::LeanObject;
pub static l_Array_term___x7e___00__closed__11_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_term___x7e___00__closed__2_value)
                as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_term___x7e___00__closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_term___x7e___00__closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term___x7e___00__closed__11_value) as *mut leanh::LeanObject;
pub static mut l_Array_term___x7e__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_term___x7e___00__closed__11_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__3_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__3_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__5_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [80, 101, 114, 109, 0]};
static mut l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__5_value) as *mut leanh::LeanObject;
static mut l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__5_value) as *mut leanh::LeanObject,6725144291058853725 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__7_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array_term___x7e___00__closed__0_value) as *mut leanh::LeanObject,8749134177695247953 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__5_value) as *mut leanh::LeanObject,8938005086969339391 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__9_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__8_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__10_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__8_value) as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__11_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 105, 115, 116, 0]};
static mut l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__11_value) as *mut leanh::LeanObject;
static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__12_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__11_value) as *mut leanh::LeanObject,9582258842178272501 as *mut leanh::LeanObject] };
pub static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__12_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__5_value) as *mut leanh::LeanObject,6626821958560496499 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__13_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__12_value) as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__14_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__13_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__15_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__10_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__14_value) as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__15_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__16_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__9_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__15_value) as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__16_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__17_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__17_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__18_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__17_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__18_value) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__0_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__1_value
) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_171_ =
        l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__5;
    v___x_172_ = l_String_toRawSubstring_x27(v___x_171_);
    return v___x_172_;
}
pub unsafe fn l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1(
    mut v_x_201_: *mut leanh::LeanObject,
    mut v_a_202_: *mut leanh::LeanObject,
    mut v_a_203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_205_: u8 = 0;
    v___x_204_ = l_Array_term___x7e___00__closed__2;
    leanh::lean_inc(v_x_201_);
    v___x_205_ = l_Lean_Syntax_isOfKind(v_x_201_, v___x_204_);
    if v___x_205_ == 0 {
        let mut v___x_206_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_207_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_201_);
        v___x_206_ = leanh::lean_box(1);
        v___x_207_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_207_, 0, v___x_206_);
        leanh::lean_ctor_set(v___x_207_, 1, v_a_203_);
        return v___x_207_;
    } else {
        let mut v_quotContext_208_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_209_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_210_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_211_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_212_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_214_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_215_: u8 = 0;
        let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_222_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_223_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_224_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_226_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_208_ = leanh::lean_ctor_get(v_a_202_, 1);
        v_currMacroScope_209_ = leanh::lean_ctor_get(v_a_202_, 2);
        v_ref_210_ = leanh::lean_ctor_get(v_a_202_, 5);
        v___x_211_ = leanh::lean_unsigned_to_nat(0);
        v___x_212_ = l_Lean_Syntax_getArg(v_x_201_, v___x_211_);
        v___x_213_ = leanh::lean_unsigned_to_nat(2);
        v___x_214_ = l_Lean_Syntax_getArg(v_x_201_, v___x_213_);
        leanh::lean_dec(v_x_201_);
        v___x_215_ = 0;
        v___x_216_ = l_Lean_SourceInfo_fromRef(v_ref_210_, v___x_215_);
        v___x_217_ = l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4;
        v___x_218_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__6), core::ptr::addr_of_mut!(l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__6_once), _init_l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__6);
        v___x_219_ = l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__7;
        leanh::lean_inc(v_currMacroScope_209_);
        leanh::lean_inc(v_quotContext_208_);
        v___x_220_ = l_Lean_addMacroScope(v_quotContext_208_, v___x_219_, v_currMacroScope_209_);
        v___x_221_ = l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__16;
        leanh::lean_inc_n(v___x_216_, 2);
        v___x_222_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_222_, 0, v___x_216_);
        leanh::lean_ctor_set(v___x_222_, 1, v___x_218_);
        leanh::lean_ctor_set(v___x_222_, 2, v___x_220_);
        leanh::lean_ctor_set(v___x_222_, 3, v___x_221_);
        v___x_223_ = l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__18;
        v___x_224_ = l_Lean_Syntax_node2(v___x_216_, v___x_223_, v___x_212_, v___x_214_);
        v___x_225_ = l_Lean_Syntax_node2(v___x_216_, v___x_217_, v___x_222_, v___x_224_);
        v___x_226_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_226_, 0, v___x_225_);
        leanh::lean_ctor_set(v___x_226_, 1, v_a_203_);
        return v___x_226_;
    }
}
pub unsafe fn l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___boxed(
    mut v_x_227_: *mut leanh::LeanObject,
    mut v_a_228_: *mut leanh::LeanObject,
    mut v_a_229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_230_ = l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1(
        v_x_227_, v_a_228_, v_a_229_,
    );
    leanh::lean_dec_ref(v_a_228_);
    return v_res_230_;
}
pub unsafe fn l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1(
    mut v_x_234_: *mut leanh::LeanObject,
    mut v_a_235_: *mut leanh::LeanObject,
    mut v_a_236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_238_: u8 = 0;
    v___x_237_ =
        l_Array___aux__Init__Data__Array__Perm______macroRules__Array__term___x7e____1___closed__4;
    leanh::lean_inc(v_x_234_);
    v___x_238_ = l_Lean_Syntax_isOfKind(v_x_234_, v___x_237_);
    if v___x_238_ == 0 {
        let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_234_);
        v___x_239_ = leanh::lean_box(0);
        v___x_240_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_240_, 0, v___x_239_);
        leanh::lean_ctor_set(v___x_240_, 1, v_a_236_);
        return v___x_240_;
    } else {
        let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_242_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_243_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_244_: u8 = 0;
        v___x_241_ = leanh::lean_unsigned_to_nat(0);
        v___x_242_ = l_Lean_Syntax_getArg(v_x_234_, v___x_241_);
        v___x_243_ =
            l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___closed__1;
        leanh::lean_inc(v___x_242_);
        v___x_244_ = l_Lean_Syntax_isOfKind(v___x_242_, v___x_243_);
        if v___x_244_ == 0 {
            let mut v___x_245_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_246_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_242_);
            leanh::lean_dec(v_x_234_);
            v___x_245_ = leanh::lean_box(0);
            v___x_246_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_246_, 0, v___x_245_);
            leanh::lean_ctor_set(v___x_246_, 1, v_a_236_);
            return v___x_246_;
        } else {
            let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_248_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_249_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_250_: u8 = 0;
            v___x_247_ = leanh::lean_unsigned_to_nat(1);
            v___x_248_ = l_Lean_Syntax_getArg(v_x_234_, v___x_247_);
            leanh::lean_dec(v_x_234_);
            v___x_249_ = leanh::lean_unsigned_to_nat(2);
            leanh::lean_inc(v___x_248_);
            v___x_250_ = l_Lean_Syntax_matchesNull(v___x_248_, v___x_249_);
            if v___x_250_ == 0 {
                let mut v___x_251_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_248_);
                leanh::lean_dec(v___x_242_);
                v___x_251_ = leanh::lean_box(0);
                v___x_252_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_252_, 0, v___x_251_);
                leanh::lean_ctor_set(v___x_252_, 1, v_a_236_);
                return v___x_252_;
            } else {
                let mut v___x_253_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_255_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_256_: u8 = 0;
                let mut v___x_257_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_258_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_259_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_261_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_262_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_253_ = l_Lean_Syntax_getArg(v___x_248_, v___x_241_);
                v___x_254_ = l_Lean_Syntax_getArg(v___x_248_, v___x_247_);
                leanh::lean_dec(v___x_248_);
                v_ref_255_ = l_Lean_replaceRef(v___x_242_, v_a_235_);
                leanh::lean_dec(v___x_242_);
                v___x_256_ = 0;
                v___x_257_ = l_Lean_SourceInfo_fromRef(v_ref_255_, v___x_256_);
                leanh::lean_dec(v_ref_255_);
                v___x_258_ = l_Array_term___x7e___00__closed__2;
                v___x_259_ = l_Array_term___x7e___00__closed__5;
                leanh::lean_inc(v___x_257_);
                v___x_260_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_260_, 0, v___x_257_);
                leanh::lean_ctor_set(v___x_260_, 1, v___x_259_);
                v___x_261_ =
                    l_Lean_Syntax_node3(v___x_257_, v___x_258_, v___x_253_, v___x_260_, v___x_254_);
                v___x_262_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_262_, 0, v___x_261_);
                leanh::lean_ctor_set(v___x_262_, 1, v_a_236_);
                return v___x_262_;
            }
        }
    }
}
pub unsafe fn l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1___boxed(
    mut v_x_263_: *mut leanh::LeanObject,
    mut v_a_264_: *mut leanh::LeanObject,
    mut v_a_265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_266_ = l_Array___aux__Init__Data__Array__Perm______unexpand__Array__Perm__1(
        v_x_263_, v_a_264_, v_a_265_,
    );
    leanh::lean_dec(v_a_264_);
    return v_res_266_;
}
pub unsafe fn l_Array_instTransPerm(
    mut v_00_u03b1_267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_268_ = leanh::lean_box(0);
    return v___x_268_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Perm(
    builtin: u8,
) -> *mut leanh::LeanObject {
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
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Perm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Perm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Perm(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Perm(builtin: u8) -> *mut leanh::LeanObject {
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
    res = initialize_Init_Data_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_Perm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Perm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Perm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Perm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_Perm(builtin);
}