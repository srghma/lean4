// Lean compiler output
// Module: Init.Data.UInt.Bitwise
// Imports: Init.Data.BitVec.Basic Init.Data.UInt.Basic Init.Data.Nat.Bitwise Init.Data.Nat.Lemmas Init.Data.UInt.Basic Init.Ext Init.Data.BitVec.Bootstrap Init.Data.BitVec.Lemmas Init.Data.Fin.Bitwise Init.Data.UInt.Lemmas Init.System.Platform
use crate::ffi::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::r#gen::Init::Data::BitVec::Basic::{
    initialize_Init_Data_BitVec_Basic, runtime_initialize_Init_Data_BitVec_Basic,
};
use crate::r#gen::Init::Data::BitVec::Bootstrap::{
    initialize_Init_Data_BitVec_Bootstrap, runtime_initialize_Init_Data_BitVec_Bootstrap,
};
use crate::r#gen::Init::Data::BitVec::Lemmas::{
    initialize_Init_Data_BitVec_Lemmas, runtime_initialize_Init_Data_BitVec_Lemmas,
};
use crate::r#gen::Init::Data::Fin::Bitwise::{
    initialize_Init_Data_Fin_Bitwise, runtime_initialize_Init_Data_Fin_Bitwise,
};
use crate::r#gen::Init::Data::Nat::Bitwise::{
    initialize_Init_Data_Nat_Bitwise, runtime_initialize_Init_Data_Nat_Bitwise,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Data::UInt::Basic::{
    initialize_Init_Data_UInt_Basic, runtime_initialize_Init_Data_UInt_Basic,
};
use crate::r#gen::Init::Data::UInt::Lemmas::{
    initialize_Init_Data_UInt_Lemmas, runtime_initialize_Init_Data_UInt_Lemmas,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4,
    l_Lean_Syntax_node5, l_Lean_Syntax_node6, l_Lean_Syntax_node7, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::System::Platform::{
    initialize_Init_System_Platform, runtime_initialize_Init_System_Platform,
};
pub static l_commandDeclare__bitwise__uint__theorems_____00__closed__0_value:
    leanh::LeanStringObject<39> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        99, 111, 109, 109, 97, 110, 100, 68, 101, 99, 108, 97, 114, 101, 95, 98, 105, 116, 119,
        105, 115, 101, 95, 117, 105, 110, 116, 95, 116, 104, 101, 111, 114, 101, 109, 115, 95, 95,
        0,
    ],
};
static mut l_commandDeclare__bitwise__uint__theorems_____00__closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__0_value)
        as *mut leanh::LeanObject;
pub static l_commandDeclare__bitwise__uint__theorems_____00__closed__1_value:
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
        core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__0_value)
            as *mut leanh::LeanObject,
        1247042218409189095 as *mut leanh::LeanObject,
    ],
};
static mut l_commandDeclare__bitwise__uint__theorems_____00__closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_commandDeclare__bitwise__uint__theorems_____00__closed__2_value:
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
static mut l_commandDeclare__bitwise__uint__theorems_____00__closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_commandDeclare__bitwise__uint__theorems_____00__closed__3_value:
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
        core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__2_value)
            as *mut leanh::LeanObject,
        12571085391447129896 as *mut leanh::LeanObject,
    ],
};
static mut l_commandDeclare__bitwise__uint__theorems_____00__closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_commandDeclare__bitwise__uint__theorems_____00__closed__4_value:
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
        100, 101, 99, 108, 97, 114, 101, 95, 98, 105, 116, 119, 105, 115, 101, 95, 117, 105, 110,
        116, 95, 116, 104, 101, 111, 114, 101, 109, 115, 0,
    ],
};
static mut l_commandDeclare__bitwise__uint__theorems_____00__closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_commandDeclare__bitwise__uint__theorems_____00__closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_commandDeclare__bitwise__uint__theorems_____00__closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_commandDeclare__bitwise__uint__theorems_____00__closed__6_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_commandDeclare__bitwise__uint__theorems_____00__closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_commandDeclare__bitwise__uint__theorems_____00__closed__7_value:
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
        core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__6_value)
            as *mut leanh::LeanObject,
        5117844058249666356 as *mut leanh::LeanObject,
    ],
};
static mut l_commandDeclare__bitwise__uint__theorems_____00__closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_commandDeclare__bitwise__uint__theorems_____00__closed__8_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_commandDeclare__bitwise__uint__theorems_____00__closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__8_value)
        as *mut leanh::LeanObject;
pub static l_commandDeclare__bitwise__uint__theorems_____00__closed__9_value:
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
        core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_commandDeclare__bitwise__uint__theorems_____00__closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__9_value)
        as *mut leanh::LeanObject;
pub static l_commandDeclare__bitwise__uint__theorems_____00__closed__10_value:
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
static mut l_commandDeclare__bitwise__uint__theorems_____00__closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__10_value)
        as *mut leanh::LeanObject;
pub static l_commandDeclare__bitwise__uint__theorems_____00__closed__11_value:
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
        core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__10_value)
            as *mut leanh::LeanObject,
        8609355255726335675 as *mut leanh::LeanObject,
    ],
};
static mut l_commandDeclare__bitwise__uint__theorems_____00__closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__11_value)
        as *mut leanh::LeanObject;
pub static l_commandDeclare__bitwise__uint__theorems_____00__closed__12_value:
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
        core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__11_value)
            as *mut leanh::LeanObject,
        (((1023 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_commandDeclare__bitwise__uint__theorems_____00__closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__12_value)
        as *mut leanh::LeanObject;
pub static l_commandDeclare__bitwise__uint__theorems_____00__closed__13_value:
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
        core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__12_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_commandDeclare__bitwise__uint__theorems_____00__closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__13_value)
        as *mut leanh::LeanObject;
pub static l_commandDeclare__bitwise__uint__theorems_____00__closed__14_value:
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
        core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__1_value)
            as *mut leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__13_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_commandDeclare__bitwise__uint__theorems_____00__closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__14_value)
        as *mut leanh::LeanObject;
pub static mut l_commandDeclare__bitwise__uint__theorems____: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__uint__theorems_____00__closed__14_value)
        as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__0_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__0_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__1_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__4_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__4_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__5_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [110, 97, 109, 101, 115, 112, 97, 99, 101, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__5_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__4_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__5_value) as *mut leanh::LeanObject,17575194138276270420 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__6_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__7_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__7_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__8_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__4_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__8_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__7_value) as *mut leanh::LeanObject,8497769072906204829 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__8_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__9_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__9_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__10_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__10_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__10_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__4_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__10_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__9_value) as *mut leanh::LeanObject,14557702332550915328 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__10_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__12_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__12_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__13_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__13_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__14_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__14_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__14_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__14_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__14_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__12_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__14_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__13_value) as *mut leanh::LeanObject,2533412339571800130 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__14_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__15_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [64, 91, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__15_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__16_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__16_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__17_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__17_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__17_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__17_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__17_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__12_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__17_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__16_value) as *mut leanh::LeanObject,7499624980761693169 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__17_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__18_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__18_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__19_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__19_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__19_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__19_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__19_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__12_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__19_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__19_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__18_value) as *mut leanh::LeanObject,7983999284776576032 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__19_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__20_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__20_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__21_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__21_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__22_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__22_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__22_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__22_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__22_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__20_value) as *mut leanh::LeanObject,4584992172905639687 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__22_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__22_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__21_value) as *mut leanh::LeanObject,1018263045977948327 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__22_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__23_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__23_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__24_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 108, 101, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__24_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__25_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__25_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__25_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__25_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__25_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__20_value) as *mut leanh::LeanObject,4584992172905639687 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__25_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__25_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__24_value) as *mut leanh::LeanObject,3878072352281346923 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__25_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__26_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [105, 110, 116, 95, 116, 111, 66, 105, 116, 86, 101, 99, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__26_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__27_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__27: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__28_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__26_value) as *mut leanh::LeanObject,1350029983115203158 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__28_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__29_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__29_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__30_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [112, 114, 111, 116, 101, 99, 116, 101, 100, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__30_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__31_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__31_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__31_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__31_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__31_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__4_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__31_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__31_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__30_value) as *mut leanh::LeanObject,14373170258808360993 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__31_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__32_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 104, 101, 111, 114, 101, 109, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__32_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__33_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__33_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__33_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__33_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__33_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__4_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__33_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__33_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__32_value) as *mut leanh::LeanObject,3907549710869165294 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__33: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__33_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__34_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 108, 73, 100, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__34: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__34_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__35_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__35_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__35_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__35_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__35_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__4_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__35_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__35_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__34_value) as *mut leanh::LeanObject,1827444229220621555 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__35: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__35_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__36_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 95, 110, 111, 116, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__36: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__36_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__37_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__37: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__38_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__36_value) as *mut leanh::LeanObject,9522006584491685636 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__38: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__38_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__39_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 99, 108, 83, 105, 103, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__39: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__39_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__40_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__40_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__40_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__40_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__40_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__4_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__40_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__40_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__39_value) as *mut leanh::LeanObject,5940551064397964566 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__40: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__40_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__41_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 109, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__41: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__41_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__42_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__42_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__42_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__42_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__42_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__12_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__42_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__42_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__41_value) as *mut leanh::LeanObject,6962862263136859431 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__42: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__42_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__43_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [123, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__43: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__43_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__44_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [97, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__44: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__44_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__45_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__45: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__46_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__44_value) as *mut leanh::LeanObject,7839396180116328695 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__46: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__46_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__47_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__47: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__47_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__48_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [125, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__48: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__48_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__49_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__49: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__49_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__50_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__50_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__50_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__50_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__50_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__12_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__50_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__50_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__49_value) as *mut leanh::LeanObject,4498178684837002829 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__50: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__50_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__51_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 95, 61, 95, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__51: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__51_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__52_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__51_value) as *mut leanh::LeanObject,5677895497334651815 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__52: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__52_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__53_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 114, 111, 106, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__53: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__53_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__54_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__54_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__54_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__54_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__54_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__12_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__54_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__54_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__53_value) as *mut leanh::LeanObject,5353940006376281447 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__54: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__54_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__55_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__55: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__55_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__56_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__56_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__56_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__56_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__56_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__12_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__56_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__56_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__55_value) as *mut leanh::LeanObject,7932075773091973500 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__56: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__56_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__57_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__57: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__57_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__58_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__58_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__58_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__58_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__58_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__12_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__58_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__58_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__57_value) as *mut leanh::LeanObject,7306243862518720553 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__58: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__58_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__59_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__59: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__59_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__60_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__60: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__60_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__61_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__60_value) as *mut leanh::LeanObject,9871775667037945883 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__61: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__61_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__62_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__62: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__62_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__63_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__63: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__64_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 101, 114, 109, 126, 126, 126, 95, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__64: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__64_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__65_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__64_value) as *mut leanh::LeanObject,244005051970854221 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__65: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__65_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__66_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [126, 126, 126, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__66: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__66_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__67_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__67: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__67_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__68_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__68: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__68_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__69_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__69: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__69_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__70_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__70: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__71_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__69_value) as *mut leanh::LeanObject,8767050042937596034 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__71: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__71_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__72_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [61, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__72: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__72_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__73_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 46, 116, 111, 66, 105, 116, 86, 101, 99, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__73: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__73_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__74_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__74: *mut leanh::LeanObject = core::ptr::null_mut();
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__75_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__44_value) as *mut leanh::LeanObject,7839396180116328695 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__75_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__75_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__69_value) as *mut leanh::LeanObject,16071506607298534126 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__75: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__75_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__76_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__76: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__76_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__77_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__77_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__77_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__77_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__77_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__4_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__77_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__77_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__76_value) as *mut leanh::LeanObject,13585030837571646948 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__77: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__77_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__78_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__78: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__78_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__79_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [114, 102, 108, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__79: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__79_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__80_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__80: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__81_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__79_value) as *mut leanh::LeanObject,17342663138809293389 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__81: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__81_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__82_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__82: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__82_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__83_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 117, 102, 102, 105, 120, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__83: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__83_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__84_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__84_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__84_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__84_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__84_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__82_value) as *mut leanh::LeanObject,7625897890118033792 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__84_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__84_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__83_value) as *mut leanh::LeanObject,8715860392475343861 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__84: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__84_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__85_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 95, 97, 110, 100, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__85: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__85_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__86_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__86: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__87_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__85_value) as *mut leanh::LeanObject,4445789131909237106 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__87: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__87_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__88_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 120, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__88: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__88_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__89_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__89_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__89_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__89_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__89_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__12_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__89_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__89_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__88_value) as *mut leanh::LeanObject,17201320286889277233 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__89: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__89_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__90_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [98, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__90: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__90_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__91_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__91: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__92_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__90_value) as *mut leanh::LeanObject,10300200614825825839 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__92: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__92_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__93_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 95, 38, 38, 38, 95, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__93: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__93_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__94_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__93_value) as *mut leanh::LeanObject,12444694952413782977 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__94: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__94_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__95_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [38, 38, 38, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__95: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__95_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__96_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [98, 46, 116, 111, 66, 105, 116, 86, 101, 99, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__96: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__96_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__97_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__97: *mut leanh::LeanObject = core::ptr::null_mut();
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__98_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__90_value) as *mut leanh::LeanObject,10300200614825825839 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__98_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__98_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__69_value) as *mut leanh::LeanObject,11947561764753763078 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__98: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__98_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__99_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 95, 111, 114, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__99: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__99_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__100_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__100: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__101_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__99_value) as *mut leanh::LeanObject,9489450475637686356 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__101: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__101_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__102_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 95, 124, 124, 124, 95, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__102: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__102_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__103_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__102_value) as *mut leanh::LeanObject,4575865287391746539 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__103: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__103_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__104_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [124, 124, 124, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__104: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__104_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__105_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 95, 120, 111, 114, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__105: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__105_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__106_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__106: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__107_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__105_value) as *mut leanh::LeanObject,2701889046734724230 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__107: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__107_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__108_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 95, 94, 94, 94, 95, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__108: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__108_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__109_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__108_value) as *mut leanh::LeanObject,4276624985753043280 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__109: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__109_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__110_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [94, 94, 94, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__110: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__110_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__111_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 95, 115, 104, 105, 102, 116, 76, 101, 102, 116, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__111: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__111_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__112_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__112: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__113_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__111_value) as *mut leanh::LeanObject,18092217254651846211 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__113: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__113_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__114_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 95, 60, 60, 60, 95, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__114: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__114_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__115_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__114_value) as *mut leanh::LeanObject,12923016781500733349 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__115: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__115_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__116_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [60, 60, 60, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__116: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__116_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__117_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 95, 37, 95, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__117: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__117_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__118_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__117_value) as *mut leanh::LeanObject,15774053547144697567 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__118: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__118_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__119_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [37, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__119: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__119_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__120_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 95, 115, 104, 105, 102, 116, 82, 105, 103, 104, 116, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__120: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__120_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__121_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__121: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__122_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__120_value) as *mut leanh::LeanObject,4071013895811443549 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__122: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__122_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__123_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 95, 62, 62, 62, 95, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__123: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__123_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__124_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__123_value) as *mut leanh::LeanObject,3619840007123166506 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__124: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__124_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__125_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [62, 62, 62, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__125: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__125_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__126_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 111, 78, 97, 116, 95, 97, 110, 100, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__126: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__126_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__127_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__127: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__128_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__126_value) as *mut leanh::LeanObject,15117902275809254386 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__128: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__128_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__129_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 78, 97, 116, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__129: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__129_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__130_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__130: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__131_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__129_value) as *mut leanh::LeanObject,8495652807202281365 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__131: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__131_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__132_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [97, 46, 116, 111, 78, 97, 116, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__132: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__132_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__133_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__133: *mut leanh::LeanObject = core::ptr::null_mut();
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__134_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__44_value) as *mut leanh::LeanObject,7839396180116328695 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__134_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__134_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__129_value) as *mut leanh::LeanObject,2959166939384111569 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__134: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__134_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__135_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [98, 46, 116, 111, 78, 97, 116, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__135: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__135_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__136_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__136: *mut leanh::LeanObject = core::ptr::null_mut();
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__137_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__90_value) as *mut leanh::LeanObject,10300200614825825839 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__137_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__137_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__129_value) as *mut leanh::LeanObject,15591306193689465273 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__137: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__137_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__138_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 121, 84, 97, 99, 116, 105, 99, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__138: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__138_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__139_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__139_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__139_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__139_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__139_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__12_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__139_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__139_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__138_value) as *mut leanh::LeanObject,16173796135615239867 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__139: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__139_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__140_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [98, 121, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__140: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__140_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__141_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__141: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__141_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__142_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__142: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__142_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__143_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__143_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__143_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__143_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__143_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__141_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__143_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__143_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__142_value) as *mut leanh::LeanObject,8504843326314613972 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__143: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__143_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__144_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__144: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__144_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__145_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__145_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__145_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__145_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__145_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__141_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__145_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__145_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__144_value) as *mut leanh::LeanObject,17228437386856258271 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__145: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__145_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__146_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__146_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__146_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__146_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__146_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__141_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__146_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__146_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__21_value) as *mut leanh::LeanObject,12783917532758215986 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__146: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__146_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__147_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__147: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__147_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__148_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__148_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__148_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__148_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__148_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__141_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__148_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__148_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__147_value) as *mut leanh::LeanObject,3488656302031949961 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__148: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__148_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__149_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__149: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__149_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__150_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 105, 109, 112, 76, 101, 109, 109, 97, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__150: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__150_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__151_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__151_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__151_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__151_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__151_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__141_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__151_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__151_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__150_value) as *mut leanh::LeanObject,7383208167966365478 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__151: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__151_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__152_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 105, 109, 112, 69, 114, 97, 115, 101, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__152: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__152_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__153_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__153_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__153_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__153_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__153_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__141_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__153_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__153_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__152_value) as *mut leanh::LeanObject,11353779426050775256 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__153: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__153_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__154_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [45, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__154: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__154_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__155_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 111, 78, 97, 116, 95, 116, 111, 66, 105, 116, 86, 101, 99, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__155: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__155_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__156_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__156: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__157_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__155_value) as *mut leanh::LeanObject,8214577282300057611 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__157: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__157_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__158_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 111, 78, 97, 116, 95, 111, 114, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__158: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__158_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__159_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__159: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__160_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__158_value) as *mut leanh::LeanObject,12654132504194092830 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__160: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__160_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__161_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 111, 78, 97, 116, 95, 120, 111, 114, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__161: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__161_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__162_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__162: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__163_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__161_value) as *mut leanh::LeanObject,3022841888857957446 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__163: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__163_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__164_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [116, 111, 78, 97, 116, 95, 115, 104, 105, 102, 116, 76, 101, 102, 116, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__164: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__164_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__165_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__165: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__166_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__164_value) as *mut leanh::LeanObject,12339757948555454818 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__166: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__166_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__167_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 95, 94, 95, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__167: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__167_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__168_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__167_value) as *mut leanh::LeanObject,12619503526879214151 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__168: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__168_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__169_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 117, 109, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__169: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__169_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__170_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__169_value) as *mut leanh::LeanObject,6110315075117401315 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__170: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__170_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__171_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [50, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__171: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__171_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__172_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [94, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__172: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__172_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__173_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [116, 111, 78, 97, 116, 95, 115, 104, 105, 102, 116, 82, 105, 103, 104, 116, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__173: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__173_value) as *mut leanh::LeanObject;
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__174_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__174: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__175_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__173_value) as *mut leanh::LeanObject,1398046938476343996 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__175: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__175_value) as *mut leanh::LeanObject;
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__176_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [101, 110, 100, 0]};
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__176: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__176_value) as *mut leanh::LeanObject;
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__177_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__177_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__177_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__177_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__177_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__4_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__177_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__177_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__176_value) as *mut leanh::LeanObject,10057000334683702526 as *mut leanh::LeanObject] };
static mut l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__177: *mut leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__177_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_793_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_793_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_829_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__26;
    v___x_830_ = l_String_toRawSubstring_x27(v___x_829_);
    return v___x_830_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__37()
-> *mut leanh::LeanObject {
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_853_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__36;
    v___x_854_ = l_String_toRawSubstring_x27(v___x_853_);
    return v___x_854_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__45()
-> *mut leanh::LeanObject {
    let mut v___x_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_871_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__44;
    v___x_872_ = l_String_toRawSubstring_x27(v___x_871_);
    return v___x_872_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__63()
-> *mut leanh::LeanObject {
    let mut v___x_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_909_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__62;
    v___x_910_ = l_String_toRawSubstring_x27(v___x_909_);
    return v___x_910_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__70()
-> *mut leanh::LeanObject {
    let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_918_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__69;
    v___x_919_ = l_String_toRawSubstring_x27(v___x_918_);
    return v___x_919_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__74()
-> *mut leanh::LeanObject {
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_924_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__73;
    v___x_925_ = l_String_toRawSubstring_x27(v___x_924_);
    return v___x_925_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__80()
-> *mut leanh::LeanObject {
    let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_937_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__79;
    v___x_938_ = l_String_toRawSubstring_x27(v___x_937_);
    return v___x_938_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__86()
-> *mut leanh::LeanObject {
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_949_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__85;
    v___x_950_ = l_String_toRawSubstring_x27(v___x_949_);
    return v___x_950_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__91()
-> *mut leanh::LeanObject {
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_960_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__90;
    v___x_961_ = l_String_toRawSubstring_x27(v___x_960_);
    return v___x_961_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__97()
-> *mut leanh::LeanObject {
    let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_969_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__96;
    v___x_970_ = l_String_toRawSubstring_x27(v___x_969_);
    return v___x_970_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__100()
-> *mut leanh::LeanObject {
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_975_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__99;
    v___x_976_ = l_String_toRawSubstring_x27(v___x_975_);
    return v___x_976_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__106()
-> *mut leanh::LeanObject {
    let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_984_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__105;
    v___x_985_ = l_String_toRawSubstring_x27(v___x_984_);
    return v___x_985_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__112()
-> *mut leanh::LeanObject {
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_993_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__111;
    v___x_994_ = l_String_toRawSubstring_x27(v___x_993_);
    return v___x_994_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__121()
-> *mut leanh::LeanObject {
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1006_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__120;
    v___x_1007_ = l_String_toRawSubstring_x27(v___x_1006_);
    return v___x_1007_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__127()
-> *mut leanh::LeanObject {
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1015_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__126;
    v___x_1016_ = l_String_toRawSubstring_x27(v___x_1015_);
    return v___x_1016_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__130()
-> *mut leanh::LeanObject {
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1020_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__129;
    v___x_1021_ = l_String_toRawSubstring_x27(v___x_1020_);
    return v___x_1021_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__133()
-> *mut leanh::LeanObject {
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1025_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__132;
    v___x_1026_ = l_String_toRawSubstring_x27(v___x_1025_);
    return v___x_1026_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__136()
-> *mut leanh::LeanObject {
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1031_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__135;
    v___x_1032_ = l_String_toRawSubstring_x27(v___x_1031_);
    return v___x_1032_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__156()
-> *mut leanh::LeanObject {
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1082_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__155;
    v___x_1083_ = l_String_toRawSubstring_x27(v___x_1082_);
    return v___x_1083_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__159()
-> *mut leanh::LeanObject {
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1087_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__158;
    v___x_1088_ = l_String_toRawSubstring_x27(v___x_1087_);
    return v___x_1088_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__162()
-> *mut leanh::LeanObject {
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1092_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__161;
    v___x_1093_ = l_String_toRawSubstring_x27(v___x_1092_);
    return v___x_1093_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__165()
-> *mut leanh::LeanObject {
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1097_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__164;
    v___x_1098_ = l_String_toRawSubstring_x27(v___x_1097_);
    return v___x_1098_;
}
pub unsafe fn _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__174()
-> *mut leanh::LeanObject {
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1110_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__173;
    v___x_1111_ = l_String_toRawSubstring_x27(v___x_1110_);
    return v___x_1111_;
}
pub unsafe fn l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1(
    mut v_x_1120_: *mut leanh::LeanObject,
    mut v_a_1121_: *mut leanh::LeanObject,
    mut v_a_1122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: u8 = 0;
    v___x_1123_ = l_commandDeclare__bitwise__uint__theorems_____00__closed__1;
    leanh::lean_inc(v_x_1120_);
    v___x_1124_ = l_Lean_Syntax_isOfKind(v_x_1120_, v___x_1123_);
    if v___x_1124_ == 0 {
        let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1120_);
        v___x_1125_ = leanh::lean_box(1);
        v___x_1126_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1126_, 0, v___x_1125_);
        leanh::lean_ctor_set(v___x_1126_, 1, v_a_1122_);
        return v___x_1126_;
    } else {
        let mut v_ref_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1132_: u8 = 0;
        let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
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
        let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ref_1127_ = leanh::lean_ctor_get(v_a_1121_, 5);
        v___x_1128_ = leanh::lean_unsigned_to_nat(1);
        v___x_1129_ = l_Lean_Syntax_getArg(v_x_1120_, v___x_1128_);
        v___x_1130_ = leanh::lean_unsigned_to_nat(2);
        v___x_1131_ = l_Lean_Syntax_getArg(v_x_1120_, v___x_1130_);
        leanh::lean_dec(v_x_1120_);
        v___x_1132_ = 0;
        v___x_1133_ = l_Lean_SourceInfo_fromRef(v_ref_1127_, v___x_1132_);
        v___x_1134_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__1;
        v___x_1135_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__5;
        v___x_1136_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__6;
        leanh::lean_inc_n(v___x_1133_, 200);
        v___x_1137_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1137_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1137_, 1, v___x_1135_);
        leanh::lean_inc_n(v___x_1129_, 2);
        v___x_1138_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1136_, v___x_1137_, v___x_1129_);
        v___x_1139_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__8;
        v___x_1140_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__10;
        v___x_1141_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__11), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__11_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__11);
        v___x_1142_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_1142_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1142_, 1, v___x_1134_);
        leanh::lean_ctor_set(v___x_1142_, 2, v___x_1141_);
        v___x_1143_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__14;
        v___x_1144_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__15;
        v___x_1145_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1145_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1145_, 1, v___x_1144_);
        v___x_1146_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__17;
        v___x_1147_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__19;
        leanh::lean_inc_ref_n(v___x_1142_, 37);
        v___x_1148_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1147_, v___x_1142_);
        v___x_1149_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__21;
        v___x_1150_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__22;
        v___x_1151_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1151_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1151_, 1, v___x_1149_);
        leanh::lean_inc_ref(v___x_1151_);
        v___x_1152_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1150_,
            v___x_1151_,
            v___x_1142_,
            v___x_1142_,
            v___x_1142_,
        );
        leanh::lean_inc(v___x_1148_);
        v___x_1153_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1146_, v___x_1148_, v___x_1152_);
        v___x_1154_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__23;
        v___x_1155_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1155_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1155_, 1, v___x_1154_);
        v___x_1156_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__25;
        v___x_1157_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__27), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__27_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__27);
        v___x_1158_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__28;
        v___x_1159_ = leanh::lean_box(0);
        v___x_1160_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1160_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1160_, 1, v___x_1157_);
        leanh::lean_ctor_set(v___x_1160_, 2, v___x_1158_);
        leanh::lean_ctor_set(v___x_1160_, 3, v___x_1159_);
        v___x_1161_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1156_, v___x_1160_, v___x_1142_);
        v___x_1162_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1146_, v___x_1148_, v___x_1161_);
        leanh::lean_inc_ref(v___x_1155_);
        leanh::lean_inc(v___x_1153_);
        v___x_1163_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1134_,
            v___x_1153_,
            v___x_1155_,
            v___x_1162_,
        );
        v___x_1164_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__29;
        v___x_1165_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1165_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1165_, 1, v___x_1164_);
        leanh::lean_inc_ref_n(v___x_1165_, 2);
        leanh::lean_inc_ref(v___x_1145_);
        v___x_1166_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1143_,
            v___x_1145_,
            v___x_1163_,
            v___x_1165_,
        );
        v___x_1167_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1134_, v___x_1166_);
        v___x_1168_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__30;
        v___x_1169_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__31;
        v___x_1170_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1170_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1170_, 1, v___x_1168_);
        v___x_1171_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1169_, v___x_1170_);
        v___x_1172_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1134_, v___x_1171_);
        leanh::lean_inc(v___x_1172_);
        v___x_1173_ = l_Lean_Syntax_node7(
            v___x_1133_,
            v___x_1140_,
            v___x_1142_,
            v___x_1167_,
            v___x_1142_,
            v___x_1172_,
            v___x_1142_,
            v___x_1142_,
            v___x_1142_,
        );
        v___x_1174_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__32;
        v___x_1175_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__33;
        v___x_1176_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1176_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1176_, 1, v___x_1174_);
        v___x_1177_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__35;
        v___x_1178_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__37), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__37_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__37);
        v___x_1179_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__38;
        v___x_1180_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1180_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1180_, 1, v___x_1178_);
        leanh::lean_ctor_set(v___x_1180_, 2, v___x_1179_);
        leanh::lean_ctor_set(v___x_1180_, 3, v___x_1159_);
        v___x_1181_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1177_, v___x_1180_, v___x_1142_);
        v___x_1182_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__40;
        v___x_1183_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__42;
        v___x_1184_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__43;
        v___x_1185_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1185_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1185_, 1, v___x_1184_);
        v___x_1186_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__45), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__45_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__45);
        v___x_1187_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__46;
        v___x_1188_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1188_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1188_, 1, v___x_1186_);
        leanh::lean_ctor_set(v___x_1188_, 2, v___x_1187_);
        leanh::lean_ctor_set(v___x_1188_, 3, v___x_1159_);
        leanh::lean_inc_ref_n(v___x_1188_, 7);
        v___x_1189_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1134_, v___x_1188_);
        v___x_1190_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__47;
        v___x_1191_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1191_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1191_, 1, v___x_1190_);
        leanh::lean_inc_ref_n(v___x_1191_, 11);
        v___x_1192_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1134_, v___x_1191_, v___x_1129_);
        v___x_1193_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__48;
        v___x_1194_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1194_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1194_, 1, v___x_1193_);
        leanh::lean_inc(v___x_1192_);
        v___x_1195_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1183_,
            v___x_1185_,
            v___x_1189_,
            v___x_1192_,
            v___x_1194_,
        );
        v___x_1196_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1134_, v___x_1195_);
        v___x_1197_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__50;
        v___x_1198_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__52;
        v___x_1199_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__54;
        v___x_1200_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__56;
        v___x_1201_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__58;
        v___x_1202_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__59;
        v___x_1203_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1203_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1203_, 1, v___x_1202_);
        v___x_1204_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__61;
        v___x_1205_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__63), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__63_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__63);
        v___x_1206_ = leanh::lean_box(0);
        v___x_1207_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1207_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1207_, 1, v___x_1205_);
        leanh::lean_ctor_set(v___x_1207_, 2, v___x_1206_);
        leanh::lean_ctor_set(v___x_1207_, 3, v___x_1159_);
        v___x_1208_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1204_, v___x_1207_);
        leanh::lean_inc_ref(v___x_1203_);
        v___x_1209_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1201_, v___x_1203_, v___x_1208_);
        v___x_1210_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__65;
        v___x_1211_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__66;
        v___x_1212_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1212_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1212_, 1, v___x_1211_);
        leanh::lean_inc_ref(v___x_1212_);
        v___x_1213_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1210_, v___x_1212_, v___x_1188_);
        v___x_1214_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__67;
        v___x_1215_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1215_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1215_, 1, v___x_1214_);
        leanh::lean_inc_ref_n(v___x_1215_, 9);
        leanh::lean_inc_n(v___x_1209_, 8);
        v___x_1216_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1200_,
            v___x_1209_,
            v___x_1213_,
            v___x_1215_,
        );
        v___x_1217_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__68;
        v___x_1218_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1218_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1218_, 1, v___x_1217_);
        v___x_1219_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__70), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__70_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__70);
        v___x_1220_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__71;
        v___x_1221_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1221_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1221_, 1, v___x_1219_);
        leanh::lean_ctor_set(v___x_1221_, 2, v___x_1220_);
        leanh::lean_ctor_set(v___x_1221_, 3, v___x_1159_);
        leanh::lean_inc_ref_n(v___x_1221_, 5);
        leanh::lean_inc_ref_n(v___x_1218_, 10);
        v___x_1222_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1199_,
            v___x_1216_,
            v___x_1218_,
            v___x_1221_,
        );
        v___x_1223_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__72;
        v___x_1224_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1224_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1224_, 1, v___x_1223_);
        v___x_1225_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__74), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__74_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__74);
        v___x_1226_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__75;
        v___x_1227_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1227_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1227_, 1, v___x_1225_);
        leanh::lean_ctor_set(v___x_1227_, 2, v___x_1226_);
        leanh::lean_ctor_set(v___x_1227_, 3, v___x_1159_);
        leanh::lean_inc_ref_n(v___x_1227_, 5);
        v___x_1228_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1210_, v___x_1212_, v___x_1227_);
        leanh::lean_inc_ref_n(v___x_1224_, 10);
        v___x_1229_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1198_,
            v___x_1222_,
            v___x_1224_,
            v___x_1228_,
        );
        v___x_1230_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1197_, v___x_1191_, v___x_1229_);
        v___x_1231_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1182_, v___x_1196_, v___x_1230_);
        v___x_1232_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__77;
        v___x_1233_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__78;
        v___x_1234_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1234_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1234_, 1, v___x_1233_);
        v___x_1235_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__80), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__80_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__80);
        v___x_1236_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__81;
        v___x_1237_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1237_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1237_, 1, v___x_1235_);
        leanh::lean_ctor_set(v___x_1237_, 2, v___x_1236_);
        leanh::lean_ctor_set(v___x_1237_, 3, v___x_1159_);
        v___x_1238_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1200_,
            v___x_1209_,
            v___x_1237_,
            v___x_1215_,
        );
        v___x_1239_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__84;
        v___x_1240_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1239_, v___x_1142_, v___x_1142_);
        leanh::lean_inc(v___x_1240_);
        leanh::lean_inc_ref(v___x_1234_);
        v___x_1241_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1232_,
            v___x_1234_,
            v___x_1238_,
            v___x_1240_,
            v___x_1142_,
        );
        leanh::lean_inc_n(v___x_1241_, 5);
        leanh::lean_inc_ref_n(v___x_1176_, 10);
        v___x_1242_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1175_,
            v___x_1176_,
            v___x_1181_,
            v___x_1231_,
            v___x_1241_,
        );
        leanh::lean_inc_n(v___x_1173_, 5);
        v___x_1243_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1139_, v___x_1173_, v___x_1242_);
        v___x_1244_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__86), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__86_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__86);
        v___x_1245_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__87;
        v___x_1246_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1246_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1246_, 1, v___x_1244_);
        leanh::lean_ctor_set(v___x_1246_, 2, v___x_1245_);
        leanh::lean_ctor_set(v___x_1246_, 3, v___x_1159_);
        v___x_1247_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1177_, v___x_1246_, v___x_1142_);
        v___x_1248_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__89;
        v___x_1249_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__91), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__91_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__91);
        v___x_1250_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__92;
        v___x_1251_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1251_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1251_, 1, v___x_1249_);
        leanh::lean_ctor_set(v___x_1251_, 2, v___x_1250_);
        leanh::lean_ctor_set(v___x_1251_, 3, v___x_1159_);
        leanh::lean_inc_ref_n(v___x_1251_, 5);
        v___x_1252_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1134_, v___x_1188_, v___x_1251_);
        v___x_1253_ = l_Lean_Syntax_node5(
            v___x_1133_,
            v___x_1248_,
            v___x_1203_,
            v___x_1252_,
            v___x_1192_,
            v___x_1142_,
            v___x_1215_,
        );
        v___x_1254_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1134_, v___x_1253_);
        v___x_1255_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__94;
        v___x_1256_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__95;
        v___x_1257_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1257_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1257_, 1, v___x_1256_);
        leanh::lean_inc_ref_n(v___x_1257_, 2);
        v___x_1258_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1255_,
            v___x_1188_,
            v___x_1257_,
            v___x_1251_,
        );
        v___x_1259_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1200_,
            v___x_1209_,
            v___x_1258_,
            v___x_1215_,
        );
        leanh::lean_inc(v___x_1259_);
        v___x_1260_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1199_,
            v___x_1259_,
            v___x_1218_,
            v___x_1221_,
        );
        v___x_1261_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__97), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__97_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__97);
        v___x_1262_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__98;
        v___x_1263_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1263_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1263_, 1, v___x_1261_);
        leanh::lean_ctor_set(v___x_1263_, 2, v___x_1262_);
        leanh::lean_ctor_set(v___x_1263_, 3, v___x_1159_);
        leanh::lean_inc_ref_n(v___x_1263_, 3);
        v___x_1264_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1255_,
            v___x_1227_,
            v___x_1257_,
            v___x_1263_,
        );
        v___x_1265_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1198_,
            v___x_1260_,
            v___x_1224_,
            v___x_1264_,
        );
        v___x_1266_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1197_, v___x_1191_, v___x_1265_);
        leanh::lean_inc_n(v___x_1254_, 9);
        v___x_1267_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1182_, v___x_1254_, v___x_1266_);
        v___x_1268_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1175_,
            v___x_1176_,
            v___x_1247_,
            v___x_1267_,
            v___x_1241_,
        );
        v___x_1269_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1139_, v___x_1173_, v___x_1268_);
        v___x_1270_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__100), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__100_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__100);
        v___x_1271_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__101;
        v___x_1272_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1272_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1272_, 1, v___x_1270_);
        leanh::lean_ctor_set(v___x_1272_, 2, v___x_1271_);
        leanh::lean_ctor_set(v___x_1272_, 3, v___x_1159_);
        v___x_1273_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1177_, v___x_1272_, v___x_1142_);
        v___x_1274_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__103;
        v___x_1275_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__104;
        v___x_1276_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1276_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1276_, 1, v___x_1275_);
        leanh::lean_inc_ref_n(v___x_1276_, 2);
        v___x_1277_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1274_,
            v___x_1188_,
            v___x_1276_,
            v___x_1251_,
        );
        v___x_1278_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1200_,
            v___x_1209_,
            v___x_1277_,
            v___x_1215_,
        );
        leanh::lean_inc(v___x_1278_);
        v___x_1279_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1199_,
            v___x_1278_,
            v___x_1218_,
            v___x_1221_,
        );
        v___x_1280_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1274_,
            v___x_1227_,
            v___x_1276_,
            v___x_1263_,
        );
        v___x_1281_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1198_,
            v___x_1279_,
            v___x_1224_,
            v___x_1280_,
        );
        v___x_1282_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1197_, v___x_1191_, v___x_1281_);
        v___x_1283_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1182_, v___x_1254_, v___x_1282_);
        v___x_1284_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1175_,
            v___x_1176_,
            v___x_1273_,
            v___x_1283_,
            v___x_1241_,
        );
        v___x_1285_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1139_, v___x_1173_, v___x_1284_);
        v___x_1286_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__106), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__106_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__106);
        v___x_1287_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__107;
        v___x_1288_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1288_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1288_, 1, v___x_1286_);
        leanh::lean_ctor_set(v___x_1288_, 2, v___x_1287_);
        leanh::lean_ctor_set(v___x_1288_, 3, v___x_1159_);
        v___x_1289_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1177_, v___x_1288_, v___x_1142_);
        v___x_1290_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__109;
        v___x_1291_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__110;
        v___x_1292_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1292_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1292_, 1, v___x_1291_);
        leanh::lean_inc_ref_n(v___x_1292_, 2);
        v___x_1293_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1290_,
            v___x_1188_,
            v___x_1292_,
            v___x_1251_,
        );
        v___x_1294_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1200_,
            v___x_1209_,
            v___x_1293_,
            v___x_1215_,
        );
        leanh::lean_inc(v___x_1294_);
        v___x_1295_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1199_,
            v___x_1294_,
            v___x_1218_,
            v___x_1221_,
        );
        v___x_1296_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1290_,
            v___x_1227_,
            v___x_1292_,
            v___x_1263_,
        );
        v___x_1297_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1198_,
            v___x_1295_,
            v___x_1224_,
            v___x_1296_,
        );
        v___x_1298_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1197_, v___x_1191_, v___x_1297_);
        v___x_1299_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1182_, v___x_1254_, v___x_1298_);
        v___x_1300_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1175_,
            v___x_1176_,
            v___x_1289_,
            v___x_1299_,
            v___x_1241_,
        );
        v___x_1301_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1139_, v___x_1173_, v___x_1300_);
        v___x_1302_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__112), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__112_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__112);
        v___x_1303_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__113;
        v___x_1304_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1304_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1304_, 1, v___x_1302_);
        leanh::lean_ctor_set(v___x_1304_, 2, v___x_1303_);
        leanh::lean_ctor_set(v___x_1304_, 3, v___x_1159_);
        v___x_1305_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1177_, v___x_1304_, v___x_1142_);
        v___x_1306_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__115;
        v___x_1307_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__116;
        v___x_1308_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1308_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1308_, 1, v___x_1307_);
        leanh::lean_inc_ref_n(v___x_1308_, 2);
        v___x_1309_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1306_,
            v___x_1188_,
            v___x_1308_,
            v___x_1251_,
        );
        v___x_1310_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1200_,
            v___x_1209_,
            v___x_1309_,
            v___x_1215_,
        );
        leanh::lean_inc(v___x_1310_);
        v___x_1311_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1199_,
            v___x_1310_,
            v___x_1218_,
            v___x_1221_,
        );
        v___x_1312_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__118;
        v___x_1313_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__119;
        v___x_1314_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1314_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1314_, 1, v___x_1313_);
        leanh::lean_inc_n(v___x_1131_, 2);
        leanh::lean_inc_ref_n(v___x_1314_, 2);
        v___x_1315_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1312_,
            v___x_1263_,
            v___x_1314_,
            v___x_1131_,
        );
        v___x_1316_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1200_,
            v___x_1209_,
            v___x_1315_,
            v___x_1215_,
        );
        leanh::lean_inc(v___x_1316_);
        v___x_1317_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1306_,
            v___x_1227_,
            v___x_1308_,
            v___x_1316_,
        );
        v___x_1318_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1198_,
            v___x_1311_,
            v___x_1224_,
            v___x_1317_,
        );
        v___x_1319_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1197_, v___x_1191_, v___x_1318_);
        v___x_1320_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1182_, v___x_1254_, v___x_1319_);
        v___x_1321_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1175_,
            v___x_1176_,
            v___x_1305_,
            v___x_1320_,
            v___x_1241_,
        );
        v___x_1322_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1139_, v___x_1173_, v___x_1321_);
        v___x_1323_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__121), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__121_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__121);
        v___x_1324_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__122;
        v___x_1325_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1325_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1325_, 1, v___x_1323_);
        leanh::lean_ctor_set(v___x_1325_, 2, v___x_1324_);
        leanh::lean_ctor_set(v___x_1325_, 3, v___x_1159_);
        v___x_1326_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1177_, v___x_1325_, v___x_1142_);
        v___x_1327_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__124;
        v___x_1328_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__125;
        v___x_1329_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1329_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1329_, 1, v___x_1328_);
        leanh::lean_inc_ref_n(v___x_1329_, 2);
        v___x_1330_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1327_,
            v___x_1188_,
            v___x_1329_,
            v___x_1251_,
        );
        v___x_1331_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1200_,
            v___x_1209_,
            v___x_1330_,
            v___x_1215_,
        );
        leanh::lean_inc(v___x_1331_);
        v___x_1332_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1199_,
            v___x_1331_,
            v___x_1218_,
            v___x_1221_,
        );
        v___x_1333_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1327_,
            v___x_1227_,
            v___x_1329_,
            v___x_1316_,
        );
        v___x_1334_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1198_,
            v___x_1332_,
            v___x_1224_,
            v___x_1333_,
        );
        v___x_1335_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1197_, v___x_1191_, v___x_1334_);
        v___x_1336_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1182_, v___x_1254_, v___x_1335_);
        v___x_1337_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1175_,
            v___x_1176_,
            v___x_1326_,
            v___x_1336_,
            v___x_1241_,
        );
        v___x_1338_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1139_, v___x_1173_, v___x_1337_);
        v___x_1339_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1134_, v___x_1153_);
        v___x_1340_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1143_,
            v___x_1145_,
            v___x_1339_,
            v___x_1165_,
        );
        v___x_1341_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1134_, v___x_1340_);
        v___x_1342_ = l_Lean_Syntax_node7(
            v___x_1133_,
            v___x_1140_,
            v___x_1142_,
            v___x_1341_,
            v___x_1142_,
            v___x_1172_,
            v___x_1142_,
            v___x_1142_,
            v___x_1142_,
        );
        v___x_1343_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__127), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__127_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__127);
        v___x_1344_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__128;
        v___x_1345_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1345_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1345_, 1, v___x_1343_);
        leanh::lean_ctor_set(v___x_1345_, 2, v___x_1344_);
        leanh::lean_ctor_set(v___x_1345_, 3, v___x_1159_);
        v___x_1346_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1177_, v___x_1345_, v___x_1142_);
        v___x_1347_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__130), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__130_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__130);
        v___x_1348_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__131;
        v___x_1349_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1349_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1349_, 1, v___x_1347_);
        leanh::lean_ctor_set(v___x_1349_, 2, v___x_1348_);
        leanh::lean_ctor_set(v___x_1349_, 3, v___x_1159_);
        leanh::lean_inc_ref_n(v___x_1349_, 5);
        v___x_1350_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1199_,
            v___x_1259_,
            v___x_1218_,
            v___x_1349_,
        );
        v___x_1351_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__133), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__133_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__133);
        v___x_1352_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__134;
        v___x_1353_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1353_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1353_, 1, v___x_1351_);
        leanh::lean_ctor_set(v___x_1353_, 2, v___x_1352_);
        leanh::lean_ctor_set(v___x_1353_, 3, v___x_1159_);
        v___x_1354_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__136), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__136_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__136);
        v___x_1355_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__137;
        v___x_1356_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1356_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1356_, 1, v___x_1354_);
        leanh::lean_ctor_set(v___x_1356_, 2, v___x_1355_);
        leanh::lean_ctor_set(v___x_1356_, 3, v___x_1159_);
        leanh::lean_inc_ref_n(v___x_1356_, 3);
        leanh::lean_inc_ref_n(v___x_1353_, 4);
        v___x_1357_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1255_,
            v___x_1353_,
            v___x_1257_,
            v___x_1356_,
        );
        v___x_1358_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1198_,
            v___x_1350_,
            v___x_1224_,
            v___x_1357_,
        );
        v___x_1359_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1197_, v___x_1191_, v___x_1358_);
        v___x_1360_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1182_, v___x_1254_, v___x_1359_);
        v___x_1361_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__139;
        v___x_1362_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__140;
        v___x_1363_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1363_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1363_, 1, v___x_1362_);
        v___x_1364_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__143;
        v___x_1365_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__145;
        v___x_1366_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__146;
        v___x_1367_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__148;
        v___x_1368_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1367_, v___x_1142_);
        v___x_1369_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__149;
        v___x_1370_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1370_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1370_, 1, v___x_1369_);
        v___x_1371_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__151;
        v___x_1372_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1371_,
            v___x_1142_,
            v___x_1142_,
            v___x_1349_,
        );
        v___x_1373_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__153;
        v___x_1374_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__154;
        v___x_1375_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1375_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1375_, 1, v___x_1374_);
        v___x_1376_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__156), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__156_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__156);
        v___x_1377_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__157;
        v___x_1378_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1378_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1378_, 1, v___x_1376_);
        leanh::lean_ctor_set(v___x_1378_, 2, v___x_1377_);
        leanh::lean_ctor_set(v___x_1378_, 3, v___x_1159_);
        v___x_1379_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1373_, v___x_1375_, v___x_1378_);
        v___x_1380_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1134_,
            v___x_1372_,
            v___x_1155_,
            v___x_1379_,
        );
        v___x_1381_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1134_,
            v___x_1370_,
            v___x_1380_,
            v___x_1165_,
        );
        v___x_1382_ = l_Lean_Syntax_node6(
            v___x_1133_,
            v___x_1366_,
            v___x_1151_,
            v___x_1368_,
            v___x_1142_,
            v___x_1142_,
            v___x_1381_,
            v___x_1142_,
        );
        v___x_1383_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1134_, v___x_1382_);
        v___x_1384_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1365_, v___x_1383_);
        v___x_1385_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1364_, v___x_1384_);
        v___x_1386_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1361_, v___x_1363_, v___x_1385_);
        v___x_1387_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1232_,
            v___x_1234_,
            v___x_1386_,
            v___x_1240_,
            v___x_1142_,
        );
        leanh::lean_inc_n(v___x_1387_, 4);
        v___x_1388_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1175_,
            v___x_1176_,
            v___x_1346_,
            v___x_1360_,
            v___x_1387_,
        );
        leanh::lean_inc_n(v___x_1342_, 4);
        v___x_1389_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1139_, v___x_1342_, v___x_1388_);
        v___x_1390_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__159), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__159_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__159);
        v___x_1391_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__160;
        v___x_1392_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1392_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1392_, 1, v___x_1390_);
        leanh::lean_ctor_set(v___x_1392_, 2, v___x_1391_);
        leanh::lean_ctor_set(v___x_1392_, 3, v___x_1159_);
        v___x_1393_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1177_, v___x_1392_, v___x_1142_);
        v___x_1394_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1199_,
            v___x_1278_,
            v___x_1218_,
            v___x_1349_,
        );
        v___x_1395_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1274_,
            v___x_1353_,
            v___x_1276_,
            v___x_1356_,
        );
        v___x_1396_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1198_,
            v___x_1394_,
            v___x_1224_,
            v___x_1395_,
        );
        v___x_1397_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1197_, v___x_1191_, v___x_1396_);
        v___x_1398_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1182_, v___x_1254_, v___x_1397_);
        v___x_1399_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1175_,
            v___x_1176_,
            v___x_1393_,
            v___x_1398_,
            v___x_1387_,
        );
        v___x_1400_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1139_, v___x_1342_, v___x_1399_);
        v___x_1401_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__162), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__162_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__162);
        v___x_1402_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__163;
        v___x_1403_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1403_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1403_, 1, v___x_1401_);
        leanh::lean_ctor_set(v___x_1403_, 2, v___x_1402_);
        leanh::lean_ctor_set(v___x_1403_, 3, v___x_1159_);
        v___x_1404_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1177_, v___x_1403_, v___x_1142_);
        v___x_1405_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1199_,
            v___x_1294_,
            v___x_1218_,
            v___x_1349_,
        );
        v___x_1406_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1290_,
            v___x_1353_,
            v___x_1292_,
            v___x_1356_,
        );
        v___x_1407_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1198_,
            v___x_1405_,
            v___x_1224_,
            v___x_1406_,
        );
        v___x_1408_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1197_, v___x_1191_, v___x_1407_);
        v___x_1409_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1182_, v___x_1254_, v___x_1408_);
        v___x_1410_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1175_,
            v___x_1176_,
            v___x_1404_,
            v___x_1409_,
            v___x_1387_,
        );
        v___x_1411_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1139_, v___x_1342_, v___x_1410_);
        v___x_1412_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__165), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__165_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__165);
        v___x_1413_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__166;
        v___x_1414_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1414_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1414_, 1, v___x_1412_);
        leanh::lean_ctor_set(v___x_1414_, 2, v___x_1413_);
        leanh::lean_ctor_set(v___x_1414_, 3, v___x_1159_);
        v___x_1415_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1177_, v___x_1414_, v___x_1142_);
        v___x_1416_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1199_,
            v___x_1310_,
            v___x_1218_,
            v___x_1349_,
        );
        v___x_1417_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1312_,
            v___x_1356_,
            v___x_1314_,
            v___x_1131_,
        );
        v___x_1418_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1200_,
            v___x_1209_,
            v___x_1417_,
            v___x_1215_,
        );
        leanh::lean_inc(v___x_1418_);
        v___x_1419_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1306_,
            v___x_1353_,
            v___x_1308_,
            v___x_1418_,
        );
        v___x_1420_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__168;
        v___x_1421_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__170;
        v___x_1422_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__171;
        v___x_1423_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1423_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1423_, 1, v___x_1422_);
        v___x_1424_ = l_Lean_Syntax_node1(v___x_1133_, v___x_1421_, v___x_1423_);
        v___x_1425_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__172;
        v___x_1426_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1426_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1426_, 1, v___x_1425_);
        v___x_1427_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1420_,
            v___x_1424_,
            v___x_1426_,
            v___x_1131_,
        );
        v___x_1428_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1312_,
            v___x_1419_,
            v___x_1314_,
            v___x_1427_,
        );
        v___x_1429_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1198_,
            v___x_1416_,
            v___x_1224_,
            v___x_1428_,
        );
        v___x_1430_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1197_, v___x_1191_, v___x_1429_);
        v___x_1431_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1182_, v___x_1254_, v___x_1430_);
        v___x_1432_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1175_,
            v___x_1176_,
            v___x_1415_,
            v___x_1431_,
            v___x_1387_,
        );
        v___x_1433_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1139_, v___x_1342_, v___x_1432_);
        v___x_1434_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__174), core::ptr::addr_of_mut!(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__174_once), _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__174);
        v___x_1435_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__175;
        v___x_1436_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1436_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1436_, 1, v___x_1434_);
        leanh::lean_ctor_set(v___x_1436_, 2, v___x_1435_);
        leanh::lean_ctor_set(v___x_1436_, 3, v___x_1159_);
        v___x_1437_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1177_, v___x_1436_, v___x_1142_);
        v___x_1438_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1199_,
            v___x_1331_,
            v___x_1218_,
            v___x_1349_,
        );
        v___x_1439_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1327_,
            v___x_1353_,
            v___x_1329_,
            v___x_1418_,
        );
        v___x_1440_ = l_Lean_Syntax_node3(
            v___x_1133_,
            v___x_1198_,
            v___x_1438_,
            v___x_1224_,
            v___x_1439_,
        );
        v___x_1441_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1197_, v___x_1191_, v___x_1440_);
        v___x_1442_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1182_, v___x_1254_, v___x_1441_);
        v___x_1443_ = l_Lean_Syntax_node4(
            v___x_1133_,
            v___x_1175_,
            v___x_1176_,
            v___x_1437_,
            v___x_1442_,
            v___x_1387_,
        );
        v___x_1444_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1139_, v___x_1342_, v___x_1443_);
        v___x_1445_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__176;
        v___x_1446_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__177;
        v___x_1447_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1447_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1447_, 1, v___x_1445_);
        v___x_1448_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1134_, v___x_1129_, v___x_1142_);
        v___x_1449_ = l_Lean_Syntax_node2(v___x_1133_, v___x_1446_, v___x_1447_, v___x_1448_);
        v___x_1450_ = leanh::lean_unsigned_to_nat(13);
        v___x_1451_ = lean_mk_empty_array_with_capacity(v___x_1450_);
        v___x_1452_ = lean_array_push(v___x_1451_, v___x_1138_);
        v___x_1453_ = lean_array_push(v___x_1452_, v___x_1243_);
        v___x_1454_ = lean_array_push(v___x_1453_, v___x_1269_);
        v___x_1455_ = lean_array_push(v___x_1454_, v___x_1285_);
        v___x_1456_ = lean_array_push(v___x_1455_, v___x_1301_);
        v___x_1457_ = lean_array_push(v___x_1456_, v___x_1322_);
        v___x_1458_ = lean_array_push(v___x_1457_, v___x_1338_);
        v___x_1459_ = lean_array_push(v___x_1458_, v___x_1389_);
        v___x_1460_ = lean_array_push(v___x_1459_, v___x_1400_);
        v___x_1461_ = lean_array_push(v___x_1460_, v___x_1411_);
        v___x_1462_ = lean_array_push(v___x_1461_, v___x_1433_);
        v___x_1463_ = lean_array_push(v___x_1462_, v___x_1444_);
        v___x_1464_ = lean_array_push(v___x_1463_, v___x_1449_);
        v___x_1465_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_1465_, 0, v___x_1133_);
        leanh::lean_ctor_set(v___x_1465_, 1, v___x_1134_);
        leanh::lean_ctor_set(v___x_1465_, 2, v___x_1464_);
        v___x_1466_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1466_, 0, v___x_1465_);
        leanh::lean_ctor_set(v___x_1466_, 1, v_a_1122_);
        return v___x_1466_;
    }
}
pub unsafe fn l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___boxed(
    mut v_x_1467_: *mut leanh::LeanObject,
    mut v_a_1468_: *mut leanh::LeanObject,
    mut v_a_1469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1470_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1(v_x_1467_, v_a_1468_, v_a_1469_);
    leanh::lean_dec_ref(v_a_1468_);
    return v_res_1470_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_UInt_Bitwise(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Bitwise(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Bitwise(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_Platform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_UInt_Bitwise(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_UInt_Bitwise(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_BitVec_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Bitwise(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Bitwise(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_System_Platform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Bitwise(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_UInt_Bitwise(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_UInt_Bitwise(builtin);
}