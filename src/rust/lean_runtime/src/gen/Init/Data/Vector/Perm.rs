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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_once, lean_unsigned_to_nat,
};
pub static l_Vector_term___x7e___00__closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Vector_term___x7e___00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__0_value) as *mut LeanObject;
pub static l_Vector_term___x7e___00__closed__1_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Vector_term___x7e___00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__1_value) as *mut LeanObject;
static l_Vector_term___x7e___00__closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Vector_term___x7e___00__closed__0_value) as *mut LeanObject,
        2228683986675333841 as *mut LeanObject,
    ],
};
pub static l_Vector_term___x7e___00__closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Vector_term___x7e___00__closed__2_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Vector_term___x7e___00__closed__1_value) as *mut LeanObject,
        5817313725829511228 as *mut LeanObject,
    ],
};
static mut l_Vector_term___x7e___00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__2_value) as *mut LeanObject;
pub static l_Vector_term___x7e___00__closed__3_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Vector_term___x7e___00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__3_value) as *mut LeanObject;
pub static l_Vector_term___x7e___00__closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Vector_term___x7e___00__closed__3_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_Vector_term___x7e___00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__4_value) as *mut LeanObject;
pub static l_Vector_term___x7e___00__closed__5_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Vector_term___x7e___00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__5_value) as *mut LeanObject;
pub static l_Vector_term___x7e___00__closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_Vector_term___x7e___00__closed__5_value) as *mut LeanObject],
};
static mut l_Vector_term___x7e___00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__6_value) as *mut LeanObject;
pub static l_Vector_term___x7e___00__closed__7_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Vector_term___x7e___00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__7_value) as *mut LeanObject;
pub static l_Vector_term___x7e___00__closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Vector_term___x7e___00__closed__7_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_Vector_term___x7e___00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__8_value) as *mut LeanObject;
pub static l_Vector_term___x7e___00__closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Vector_term___x7e___00__closed__8_value) as *mut LeanObject,
        (((51 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Vector_term___x7e___00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__9_value) as *mut LeanObject;
pub static l_Vector_term___x7e___00__closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Vector_term___x7e___00__closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Vector_term___x7e___00__closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Vector_term___x7e___00__closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Vector_term___x7e___00__closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__10_value) as *mut LeanObject;
pub static l_Vector_term___x7e___00__closed__11_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Vector_term___x7e___00__closed__2_value) as *mut LeanObject,
        (((50 as usize) << 1) | 1) as *mut LeanObject,
        (((50 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Vector_term___x7e___00__closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Vector_term___x7e___00__closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__11_value) as *mut LeanObject;
pub static mut l_Vector_term___x7e__: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_term___x7e___00__closed__11_value) as *mut LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__0_value) as *mut LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__1_value) as *mut LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__2_value) as *mut LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__3_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__3_value) as *mut LeanObject;
static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__3_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4_value) as *mut LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [80, 101, 114, 109, 0]};
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5_value) as *mut LeanObject;
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5_value) as *mut LeanObject,6725144291058853725 as *mut LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__7_value) as *mut LeanObject;
static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Vector_term___x7e___00__closed__0_value) as *mut LeanObject,2228683986675333841 as *mut LeanObject] };
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5_value) as *mut LeanObject,8400112714772980863 as *mut LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__8_value) as *mut LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__9_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__8_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__9_value) as *mut LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__10_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__8_value) as *mut LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__10_value) as *mut LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__11_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [65, 114, 114, 97, 121, 0]};
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__11_value) as *mut LeanObject;
static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__12_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__11_value) as *mut LeanObject,8749134177695247953 as *mut LeanObject] };
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__12_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5_value) as *mut LeanObject,8938005086969339391 as *mut LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__12_value) as *mut LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__13_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__12_value) as *mut LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__13_value) as *mut LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__14_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 105, 115, 116, 0]};
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__14_value) as *mut LeanObject;
static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__15_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__14_value) as *mut LeanObject,9582258842178272501 as *mut LeanObject] };
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__15_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5_value) as *mut LeanObject,6626821958560496499 as *mut LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__15_value) as *mut LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__16_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__15_value) as *mut LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__16_value) as *mut LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__17_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__16_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__17: *mut LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__17_value) as *mut LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__18_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__13_value) as *mut LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__17_value) as *mut LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__18_value) as *mut LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__19_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__10_value) as *mut LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__18_value) as *mut LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__19: *mut LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__19_value) as *mut LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__20_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__19_value) as *mut LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__20: *mut LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__20_value) as *mut LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__21_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__21: *mut LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__21_value) as *mut LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__22_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__21_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__22: *mut LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__22_value) as *mut LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__0_value
) as *mut LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__0_value) as *mut LeanObject,5117844058249666356 as *mut LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__1_value
) as *mut LeanObject;
pub unsafe fn _init_l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__6()
-> *mut LeanObject {
    let mut v___x_184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_185_: *mut LeanObject = core::ptr::null_mut();
    v___x_184_ = l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__5;
    v___x_185_ = l_String_toRawSubstring_x27(v___x_184_);
    return v___x_185_;
}
pub unsafe fn l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1(
    mut v_x_223_: *mut LeanObject,
    mut v_a_224_: *mut LeanObject,
    mut v_a_225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_227_: u8 = 0;
    v___x_226_ = l_Vector_term___x7e___00__closed__2;
    lean_inc(v_x_223_);
    v___x_227_ = l_Lean_Syntax_isOfKind(v_x_223_, v___x_226_);
    if v___x_227_ == 0 {
        let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_223_);
        v___x_228_ = lean_box(1);
        v___x_229_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_229_, 0, v___x_228_);
        lean_ctor_set(v___x_229_, 1, v_a_225_);
        return v___x_229_;
    } else {
        let mut v_quotContext_230_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_231_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_232_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_236_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_237_: u8 = 0;
        let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_246_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_230_ = lean_ctor_get(v_a_224_, 1);
        v_currMacroScope_231_ = lean_ctor_get(v_a_224_, 2);
        v_ref_232_ = lean_ctor_get(v_a_224_, 5);
        v___x_233_ = lean_unsigned_to_nat(0);
        v___x_234_ = l_Lean_Syntax_getArg(v_x_223_, v___x_233_);
        v___x_235_ = lean_unsigned_to_nat(2);
        v___x_236_ = l_Lean_Syntax_getArg(v_x_223_, v___x_235_);
        lean_dec(v_x_223_);
        v___x_237_ = 0;
        v___x_238_ = l_Lean_SourceInfo_fromRef(v_ref_232_, v___x_237_);
        v___x_239_ = l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4;
        v___x_240_ = lean_obj_once(core::ptr::addr_of_mut!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__6), core::ptr::addr_of_mut!(l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__6_once), _init_l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__6);
        v___x_241_ = l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__7;
        lean_inc(v_currMacroScope_231_);
        lean_inc(v_quotContext_230_);
        v___x_242_ = l_Lean_addMacroScope(v_quotContext_230_, v___x_241_, v_currMacroScope_231_);
        v___x_243_ = l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__20;
        lean_inc_n(v___x_238_, 2);
        v___x_244_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_244_, 0, v___x_238_);
        lean_ctor_set(v___x_244_, 1, v___x_240_);
        lean_ctor_set(v___x_244_, 2, v___x_242_);
        lean_ctor_set(v___x_244_, 3, v___x_243_);
        v___x_245_ = l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__22;
        v___x_246_ = l_Lean_Syntax_node2(v___x_238_, v___x_245_, v___x_234_, v___x_236_);
        v___x_247_ = l_Lean_Syntax_node2(v___x_238_, v___x_239_, v___x_244_, v___x_246_);
        v___x_248_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_248_, 0, v___x_247_);
        lean_ctor_set(v___x_248_, 1, v_a_225_);
        return v___x_248_;
    }
}
pub unsafe fn l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___boxed(
    mut v_x_249_: *mut LeanObject,
    mut v_a_250_: *mut LeanObject,
    mut v_a_251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_252_: *mut LeanObject = core::ptr::null_mut();
    v_res_252_ = l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1(
        v_x_249_, v_a_250_, v_a_251_,
    );
    lean_dec_ref(v_a_250_);
    return v_res_252_;
}
pub unsafe fn l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1(
    mut v_x_256_: *mut LeanObject,
    mut v_a_257_: *mut LeanObject,
    mut v_a_258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_260_: u8 = 0;
    v___x_259_ = l_Vector___aux__Init__Data__Vector__Perm______macroRules__Vector__term___x7e____1___closed__4;
    lean_inc(v_x_256_);
    v___x_260_ = l_Lean_Syntax_isOfKind(v_x_256_, v___x_259_);
    if v___x_260_ == 0 {
        let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_262_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_256_);
        v___x_261_ = lean_box(0);
        v___x_262_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_262_, 0, v___x_261_);
        lean_ctor_set(v___x_262_, 1, v_a_258_);
        return v___x_262_;
    } else {
        let mut v___x_263_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_266_: u8 = 0;
        v___x_263_ = lean_unsigned_to_nat(0);
        v___x_264_ = l_Lean_Syntax_getArg(v_x_256_, v___x_263_);
        v___x_265_ =
            l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___closed__1;
        lean_inc(v___x_264_);
        v___x_266_ = l_Lean_Syntax_isOfKind(v___x_264_, v___x_265_);
        if v___x_266_ == 0 {
            let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_264_);
            lean_dec(v_x_256_);
            v___x_267_ = lean_box(0);
            v___x_268_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_268_, 0, v___x_267_);
            lean_ctor_set(v___x_268_, 1, v_a_258_);
            return v___x_268_;
        } else {
            let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_272_: u8 = 0;
            v___x_269_ = lean_unsigned_to_nat(1);
            v___x_270_ = l_Lean_Syntax_getArg(v_x_256_, v___x_269_);
            lean_dec(v_x_256_);
            v___x_271_ = lean_unsigned_to_nat(2);
            lean_inc(v___x_270_);
            v___x_272_ = l_Lean_Syntax_matchesNull(v___x_270_, v___x_271_);
            if v___x_272_ == 0 {
                let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_270_);
                lean_dec(v___x_264_);
                v___x_273_ = lean_box(0);
                v___x_274_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_274_, 0, v___x_273_);
                lean_ctor_set(v___x_274_, 1, v_a_258_);
                return v___x_274_;
            } else {
                let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_277_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_278_: u8 = 0;
                let mut v___x_279_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_280_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_281_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_283_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
                v___x_275_ = l_Lean_Syntax_getArg(v___x_270_, v___x_263_);
                v___x_276_ = l_Lean_Syntax_getArg(v___x_270_, v___x_269_);
                lean_dec(v___x_270_);
                v_ref_277_ = l_Lean_replaceRef(v___x_264_, v_a_257_);
                lean_dec(v___x_264_);
                v___x_278_ = 0;
                v___x_279_ = l_Lean_SourceInfo_fromRef(v_ref_277_, v___x_278_);
                lean_dec(v_ref_277_);
                v___x_280_ = l_Vector_term___x7e___00__closed__2;
                v___x_281_ = l_Vector_term___x7e___00__closed__5;
                lean_inc(v___x_279_);
                v___x_282_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_282_, 0, v___x_279_);
                lean_ctor_set(v___x_282_, 1, v___x_281_);
                v___x_283_ =
                    l_Lean_Syntax_node3(v___x_279_, v___x_280_, v___x_275_, v___x_282_, v___x_276_);
                v___x_284_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_284_, 0, v___x_283_);
                lean_ctor_set(v___x_284_, 1, v_a_258_);
                return v___x_284_;
            }
        }
    }
}
pub unsafe fn l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1___boxed(
    mut v_x_285_: *mut LeanObject,
    mut v_a_286_: *mut LeanObject,
    mut v_a_287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_288_: *mut LeanObject = core::ptr::null_mut();
    v_res_288_ = l_Vector___aux__Init__Data__Vector__Perm______unexpand__Vector__Perm__1(
        v_x_285_, v_a_286_, v_a_287_,
    );
    lean_dec(v_a_286_);
    return v_res_288_;
}
pub unsafe fn l_Vector_instTransPerm(
    mut v_00_u03b1_289_: *mut LeanObject,
    mut v_n_290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
    v___x_291_ = lean_box(0);
    return v___x_291_;
}
pub unsafe fn l_Vector_instTransPerm___boxed(
    mut v_00_u03b1_292_: *mut LeanObject,
    mut v_n_293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_294_: *mut LeanObject = core::ptr::null_mut();
    v_res_294_ = l_Vector_instTransPerm(v_00_u03b1_292_, v_n_293_);
    lean_dec(v_n_293_);
    return v_res_294_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Vector_Perm(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Perm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Perm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Vector_Perm(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Vector_Perm(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Perm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_Perm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Perm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Vector_Perm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Vector_Perm(builtin);
}
