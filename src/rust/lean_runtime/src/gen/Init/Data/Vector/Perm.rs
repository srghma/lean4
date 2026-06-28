// Lean compiler output
// Module: Init.Data.Vector.Perm
// Imports: Init.Data.Array.Basic Init.Data.Array.Perm Init.Data.Vector.Basic Init.Data.Vector.Basic Init.Data.List.Nat.Perm Init.Data.Vector.Lemmas
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Array::Perm::{
    initialize_Init_Data_Array_Perm, runtime_initialize_Init_Data_Array_Perm,
};
use crate::r#gen::Init::Data::List::Nat::Perm::{
    initialize_Init_Data_List_Nat_Perm, runtime_initialize_Init_Data_List_Nat_Perm,
};
use crate::r#gen::Init::Data::Vector::Basic::{
    initialize_Init_Data_Vector_Basic, runtime_initialize_Init_Data_Vector_Basic,
};
use crate::r#gen::Init::Data::Vector::Lemmas::{
    initialize_Init_Data_Vector_Lemmas, runtime_initialize_Init_Data_Vector_Lemmas,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_addMacroScope, l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
pub static l_Vector_term___x7e___00__closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [86, 101, 99, 116, 111, 114, 0],
    };
static mut l_Vector_term___x7e___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Vector_term___x7e___00__closed__1_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [116, 101, 114, 109, 95, 126, 95, 0],
    };
static mut l_Vector_term___x7e___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__1_value) as *mut crate::leanh::LeanObject;
static l_Vector_term___x7e___00__closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_term___x7e___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            2228683986675333841 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Vector_term___x7e___00__closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_term___x7e___00__closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_term___x7e___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            5817313725829511228 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Vector_term___x7e___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Vector_term___x7e___00__closed__3_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Vector_term___x7e___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Vector_term___x7e___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_term___x7e___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Vector_term___x7e___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Vector_term___x7e___00__closed__5_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [32, 126, 32, 0],
    };
static mut l_Vector_term___x7e___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Vector_term___x7e___00__closed__6_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Vector_term___x7e___00__closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Vector_term___x7e___00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Vector_term___x7e___00__closed__7_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Vector_term___x7e___00__closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Vector_term___x7e___00__closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_term___x7e___00__closed__7_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Vector_term___x7e___00__closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Vector_term___x7e___00__closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Vector_term___x7e___00__closed__8_value)
                as *mut crate::leanh::LeanObject,
            (((51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Vector_term___x7e___00__closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Vector_term___x7e___00__closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_term___x7e___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_term___x7e___00__closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_term___x7e___00__closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Vector_term___x7e___00__closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Vector_term___x7e___00__closed__11_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_term___x7e___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_term___x7e___00__closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Vector_term___x7e___00__closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Vector_term___x7e__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__3_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [80, 101, 114, 109, 0]};
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5_value) as *mut crate::leanh::LeanObject,6725144291058853725 as *mut crate::leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__7_value) as *mut crate::leanh::LeanObject;
static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Vector_term___x7e___00__closed__0_value) as *mut crate::leanh::LeanObject,2228683986675333841 as *mut crate::leanh::LeanObject] };
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5_value) as *mut crate::leanh::LeanObject,8400112714772980863 as *mut crate::leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__8_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__10_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__8_value) as *mut crate::leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__11_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [65, 114, 114, 97, 121, 0]};
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__11_value) as *mut crate::leanh::LeanObject;
static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__11_value) as *mut crate::leanh::LeanObject,8749134177695247953 as *mut crate::leanh::LeanObject] };
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__12_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5_value) as *mut crate::leanh::LeanObject,8938005086969339391 as *mut crate::leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__13_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__12_value) as *mut crate::leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__14_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 105, 115, 116, 0]};
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__14_value) as *mut crate::leanh::LeanObject;
static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__14_value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__15_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5_value) as *mut crate::leanh::LeanObject,6626821958560496499 as *mut crate::leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__16_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__15_value) as *mut crate::leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__17_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__16_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__18_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__13_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__17_value) as *mut crate::leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__19_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__10_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__18_value) as *mut crate::leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__20_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__19_value) as *mut crate::leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__21_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__22_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__21_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__0_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_184_ = l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5;
    v___x_185_ = l_String_toRawSubstring_x27(v___x_184_);
    return v___x_185_;
}
pub unsafe fn l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1(
    mut v_x_223_: *mut crate::leanh::LeanObject,
    mut v_a_224_: *mut crate::leanh::LeanObject,
    mut v_a_225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: u8 = 0;
    v___x_226_ = l_Vector_term___x7e___00__closed__2;
    crate::leanh::lean_inc(v_x_223_);
    v___x_227_ = l_Lean_Syntax_isOfKind(v_x_223_, v___x_226_);
    if v___x_227_ == 0 {
        let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_223_);
        v___x_228_ = crate::leanh::lean_box(1);
        v___x_229_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_229_, 0, v___x_228_);
        crate::leanh::lean_ctor_set(v___x_229_, 1, v_a_225_);
        return v___x_229_;
    } else {
        let mut v_quotContext_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_237_: u8 = 0;
        let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_230_ = crate::leanh::lean_ctor_get(v_a_224_, 1);
        v_currMacroScope_231_ = crate::leanh::lean_ctor_get(v_a_224_, 2);
        v_ref_232_ = crate::leanh::lean_ctor_get(v_a_224_, 5);
        v___x_233_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_234_ = l_Lean_Syntax_getArg(v_x_223_, v___x_233_);
        v___x_235_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_236_ = l_Lean_Syntax_getArg(v_x_223_, v___x_235_);
        crate::leanh::lean_dec(v_x_223_);
        v___x_237_ = 0;
        v___x_238_ = l_Lean_SourceInfo_fromRef(v_ref_232_, v___x_237_);
        v___x_239_ = l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4;
        v___x_240_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__6), core::ptr::addr_of_mut!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__6_once), _init_l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__6);
        v___x_241_ = l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__7;
        crate::leanh::lean_inc(v_currMacroScope_231_);
        crate::leanh::lean_inc(v_quotContext_230_);
        v___x_242_ = l_Lean_addMacroScope(v_quotContext_230_, v___x_241_, v_currMacroScope_231_);
        v___x_243_ = l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__20;
        crate::leanh::lean_inc_n(v___x_238_, 2);
        v___x_244_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_244_, 0, v___x_238_);
        crate::leanh::lean_ctor_set(v___x_244_, 1, v___x_240_);
        crate::leanh::lean_ctor_set(v___x_244_, 2, v___x_242_);
        crate::leanh::lean_ctor_set(v___x_244_, 3, v___x_243_);
        v___x_245_ = l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__22;
        v___x_246_ = l_Lean_Syntax_node2(v___x_238_, v___x_245_, v___x_234_, v___x_236_);
        v___x_247_ = l_Lean_Syntax_node2(v___x_238_, v___x_239_, v___x_244_, v___x_246_);
        v___x_248_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_248_, 0, v___x_247_);
        crate::leanh::lean_ctor_set(v___x_248_, 1, v_a_225_);
        return v___x_248_;
    }
}
pub unsafe fn l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___boxed(
    mut v_x_249_: *mut crate::leanh::LeanObject,
    mut v_a_250_: *mut crate::leanh::LeanObject,
    mut v_a_251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_252_ = l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1(
        v_x_249_, v_a_250_, v_a_251_,
    );
    crate::leanh::lean_dec_ref(v_a_250_);
    return v_res_252_;
}
pub unsafe fn l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1(
    mut v_x_256_: *mut crate::leanh::LeanObject,
    mut v_a_257_: *mut crate::leanh::LeanObject,
    mut v_a_258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_260_: u8 = 0;
    v___x_259_ = l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4;
    crate::leanh::lean_inc(v_x_256_);
    v___x_260_ = l_Lean_Syntax_isOfKind(v_x_256_, v___x_259_);
    if v___x_260_ == 0 {
        let mut v___x_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_256_);
        v___x_261_ = crate::leanh::lean_box(0);
        v___x_262_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_262_, 0, v___x_261_);
        crate::leanh::lean_ctor_set(v___x_262_, 1, v_a_258_);
        return v___x_262_;
    } else {
        let mut v___x_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_266_: u8 = 0;
        v___x_263_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_264_ = l_Lean_Syntax_getArg(v_x_256_, v___x_263_);
        v___x_265_ =
            l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__1;
        crate::leanh::lean_inc(v___x_264_);
        v___x_266_ = l_Lean_Syntax_isOfKind(v___x_264_, v___x_265_);
        if v___x_266_ == 0 {
            let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_264_);
            crate::leanh::lean_dec(v_x_256_);
            v___x_267_ = crate::leanh::lean_box(0);
            v___x_268_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_268_, 0, v___x_267_);
            crate::leanh::lean_ctor_set(v___x_268_, 1, v_a_258_);
            return v___x_268_;
        } else {
            let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_272_: u8 = 0;
            v___x_269_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_270_ = l_Lean_Syntax_getArg(v_x_256_, v___x_269_);
            crate::leanh::lean_dec(v_x_256_);
            v___x_271_ = crate::leanh::lean_unsigned_to_nat(2);
            crate::leanh::lean_inc(v___x_270_);
            v___x_272_ = l_Lean_Syntax_matchesNull(v___x_270_, v___x_271_);
            if v___x_272_ == 0 {
                let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_270_);
                crate::leanh::lean_dec(v___x_264_);
                v___x_273_ = crate::leanh::lean_box(0);
                v___x_274_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_274_, 0, v___x_273_);
                crate::leanh::lean_ctor_set(v___x_274_, 1, v_a_258_);
                return v___x_274_;
            } else {
                let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ref_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_278_: u8 = 0;
                let mut v___x_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_275_ = l_Lean_Syntax_getArg(v___x_270_, v___x_263_);
                v___x_276_ = l_Lean_Syntax_getArg(v___x_270_, v___x_269_);
                crate::leanh::lean_dec(v___x_270_);
                v_ref_277_ = l_Lean_replaceRef(v___x_264_, v_a_257_);
                crate::leanh::lean_dec(v___x_264_);
                v___x_278_ = 0;
                v___x_279_ = l_Lean_SourceInfo_fromRef(v_ref_277_, v___x_278_);
                crate::leanh::lean_dec(v_ref_277_);
                v___x_280_ = l_Vector_term___x7e___00__closed__2;
                v___x_281_ = l_Vector_term___x7e___00__closed__5;
                crate::leanh::lean_inc(v___x_279_);
                v___x_282_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_282_, 0, v___x_279_);
                crate::leanh::lean_ctor_set(v___x_282_, 1, v___x_281_);
                v___x_283_ =
                    l_Lean_Syntax_node3(v___x_279_, v___x_280_, v___x_275_, v___x_282_, v___x_276_);
                v___x_284_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_284_, 0, v___x_283_);
                crate::leanh::lean_ctor_set(v___x_284_, 1, v_a_258_);
                return v___x_284_;
            }
        }
    }
}
pub unsafe fn l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___boxed(
    mut v_x_285_: *mut crate::leanh::LeanObject,
    mut v_a_286_: *mut crate::leanh::LeanObject,
    mut v_a_287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_288_ = l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1(
        v_x_285_, v_a_286_, v_a_287_,
    );
    crate::leanh::lean_dec(v_a_286_);
    return v_res_288_;
}
pub unsafe fn l_Vector_instTransPerm(
    mut v_00_u03b1_289_: *mut crate::leanh::LeanObject,
    mut v_n_290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_291_ = crate::leanh::lean_box(0);
    return v___x_291_;
}
pub unsafe fn l_Vector_instTransPerm___boxed(
    mut v_00_u03b1_292_: *mut crate::leanh::LeanObject,
    mut v_n_293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_294_ = l_Vector_instTransPerm(v_00_u03b1_292_, v_n_293_);
    crate::leanh::lean_dec(v_n_293_);
    return v_res_294_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Vector_Perm(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Perm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Perm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Vector_Perm(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Vector_Perm(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Perm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_Perm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Perm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Vector_Perm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Vector_Perm(builtin);
}
