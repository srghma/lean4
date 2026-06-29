// Lean compiler output
// Module: Init.Data.SInt.Bitwise
// Imports: Init.Data.UInt.Basic Init.Data.BitVec.Basic Init.Data.BitVec.Lemmas Init.Data.SInt.Basic Init.Data.SInt.Basic Init.Ext Init.Data.BitVec.Bitblast Init.Data.SInt.Lemmas Init.System.Platform
use crate::r#gen::Init::Data::BitVec::Basic::{
    initialize_Init_Data_BitVec_Basic, runtime_initialize_Init_Data_BitVec_Basic,
};
use crate::r#gen::Init::Data::BitVec::Bitblast::{
    initialize_Init_Data_BitVec_Bitblast, runtime_initialize_Init_Data_BitVec_Bitblast,
};
use crate::r#gen::Init::Data::BitVec::Lemmas::{
    initialize_Init_Data_BitVec_Lemmas, runtime_initialize_Init_Data_BitVec_Lemmas,
};
use crate::r#gen::Init::Data::SInt::Basic::{
    initialize_Init_Data_SInt_Basic, runtime_initialize_Init_Data_SInt_Basic,
};
use crate::r#gen::Init::Data::SInt::Lemmas::{
    initialize_Init_Data_SInt_Lemmas, runtime_initialize_Init_Data_SInt_Lemmas,
};
use crate::r#gen::Init::Data::UInt::Basic::{
    initialize_Init_Data_UInt_Basic, runtime_initialize_Init_Data_UInt_Basic,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4,
    l_Lean_Syntax_node5, l_Lean_Syntax_node7, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::System::Platform::{
    initialize_Init_System_Platform, runtime_initialize_Init_System_Platform,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
pub static l_commandDeclare__bitwise__int__theorems_____00__closed__0_value:
    crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        99, 111, 109, 109, 97, 110, 100, 68, 101, 99, 108, 97, 114, 101, 95, 98, 105, 116, 119,
        105, 115, 101, 95, 105, 110, 116, 95, 116, 104, 101, 111, 114, 101, 109, 115, 95, 95, 0,
    ],
};
static mut l_commandDeclare__bitwise__int__theorems_____00__closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_commandDeclare__bitwise__int__theorems_____00__closed__1_value:
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
        core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        2837315325274298231 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_commandDeclare__bitwise__int__theorems_____00__closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_commandDeclare__bitwise__int__theorems_____00__closed__2_value:
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
static mut l_commandDeclare__bitwise__int__theorems_____00__closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_commandDeclare__bitwise__int__theorems_____00__closed__3_value:
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
        core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__2_value)
            as *mut crate::leanh::LeanObject,
        12571085391447129896 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_commandDeclare__bitwise__int__theorems_____00__closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_commandDeclare__bitwise__int__theorems_____00__closed__4_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        100, 101, 99, 108, 97, 114, 101, 95, 98, 105, 116, 119, 105, 115, 101, 95, 105, 110, 116,
        95, 116, 104, 101, 111, 114, 101, 109, 115, 0,
    ],
};
static mut l_commandDeclare__bitwise__int__theorems_____00__closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_commandDeclare__bitwise__int__theorems_____00__closed__5_value:
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
        core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_commandDeclare__bitwise__int__theorems_____00__closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_commandDeclare__bitwise__int__theorems_____00__closed__6_value:
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
static mut l_commandDeclare__bitwise__int__theorems_____00__closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_commandDeclare__bitwise__int__theorems_____00__closed__7_value:
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
        core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__6_value)
            as *mut crate::leanh::LeanObject,
        5117844058249666356 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_commandDeclare__bitwise__int__theorems_____00__closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_commandDeclare__bitwise__int__theorems_____00__closed__8_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_commandDeclare__bitwise__int__theorems_____00__closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_commandDeclare__bitwise__int__theorems_____00__closed__9_value:
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
        core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__5_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_commandDeclare__bitwise__int__theorems_____00__closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_commandDeclare__bitwise__int__theorems_____00__closed__10_value:
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
static mut l_commandDeclare__bitwise__int__theorems_____00__closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_commandDeclare__bitwise__int__theorems_____00__closed__11_value:
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
        core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__10_value)
            as *mut crate::leanh::LeanObject,
        8609355255726335675 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_commandDeclare__bitwise__int__theorems_____00__closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_commandDeclare__bitwise__int__theorems_____00__closed__12_value:
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
        core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__11_value)
            as *mut crate::leanh::LeanObject,
        (((1023 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_commandDeclare__bitwise__int__theorems_____00__closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_commandDeclare__bitwise__int__theorems_____00__closed__13_value:
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
        core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_commandDeclare__bitwise__int__theorems_____00__closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_commandDeclare__bitwise__int__theorems_____00__closed__14_value:
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
        core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_commandDeclare__bitwise__int__theorems_____00__closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_commandDeclare__bitwise__int__theorems____: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_commandDeclare__bitwise__int__theorems_____00__closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__0_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__5_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [110, 97, 109, 101, 115, 112, 97, 99, 101, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__5_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__5_value) as *mut crate::leanh::LeanObject,17575194138276270420 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__7_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__7_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__7_value) as *mut crate::leanh::LeanObject,8497769072906204829 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__9_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__9_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__10_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__10_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__10_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__9_value) as *mut crate::leanh::LeanObject,14557702332550915328 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__13_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__13_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__14_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__14_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__14_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__14_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__14_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__13_value) as *mut crate::leanh::LeanObject,2533412339571800130 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__15_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [64, 91, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__16_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__16_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__17_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__17_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__17_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__17_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__17_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__16_value) as *mut crate::leanh::LeanObject,7499624980761693169 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__18_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__18_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__19_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__19_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__19_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__19_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__19_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__19_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__19_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__18_value) as *mut crate::leanh::LeanObject,7983999284776576032 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__20_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__21_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__21_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__22_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__22_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__22_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__22_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__22_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__20_value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__22_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__22_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__21_value) as *mut crate::leanh::LeanObject,1018263045977948327 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__23_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__24_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 108, 101, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__24_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__25_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__25_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__25_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__25_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__25_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__20_value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__25_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__25_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__24_value) as *mut crate::leanh::LeanObject,3878072352281346923 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__26_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [105, 110, 116, 95, 116, 111, 66, 105, 116, 86, 101, 99, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__26_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__27_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__27: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__28_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__26_value) as *mut crate::leanh::LeanObject,1350029983115203158 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__29_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__30_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [112, 114, 111, 116, 101, 99, 116, 101, 100, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__30_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__31_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__31_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__31_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__31_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__31_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__31_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__31_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__30_value) as *mut crate::leanh::LeanObject,14373170258808360993 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__31_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__32_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 104, 101, 111, 114, 101, 109, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__32_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__33_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__33_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__33_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__33_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__33_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__33_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__33_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__32_value) as *mut crate::leanh::LeanObject,3907549710869165294 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__33_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__34_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 108, 73, 100, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__34: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__34_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__35_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__35_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__35_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__35_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__35_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__35_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__35_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__34_value) as *mut crate::leanh::LeanObject,1827444229220621555 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__35: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__35_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__36_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 95, 110, 111, 116, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__36_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__37_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__37: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__38_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__36_value) as *mut crate::leanh::LeanObject,9522006584491685636 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__38: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__38_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__39_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 99, 108, 83, 105, 103, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__39: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__39_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__40_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__40_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__40_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__40_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__40_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__40_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__40_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__39_value) as *mut crate::leanh::LeanObject,5940551064397964566 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__40: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__40_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__41_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 109, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__41: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__41_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__42_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__42_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__42_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__42_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__42_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__42_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__42_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__41_value) as *mut crate::leanh::LeanObject,6962862263136859431 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__42: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__42_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__43_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [123, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__43: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__43_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__44_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [97, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__44: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__44_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__45_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__45: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__46_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__44_value) as *mut crate::leanh::LeanObject,7839396180116328695 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__46: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__46_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__47_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__47: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__47_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__48_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [125, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__48: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__48_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__49_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__49: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__49_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__50_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__50_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__50_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__50_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__50_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__50_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__50_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__49_value) as *mut crate::leanh::LeanObject,4498178684837002829 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__50: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__50_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__51_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 95, 61, 95, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__51: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__51_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__52_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__51_value) as *mut crate::leanh::LeanObject,5677895497334651815 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__52: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__52_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__53_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 114, 111, 106, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__53: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__53_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__54_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__54_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__54_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__54_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__54_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__54_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__54_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__53_value) as *mut crate::leanh::LeanObject,5353940006376281447 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__54: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__54_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__55_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__55: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__55_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__56_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__56_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__56_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__56_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__56_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__56_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__56_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__55_value) as *mut crate::leanh::LeanObject,7932075773091973500 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__56: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__56_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__57_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__57: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__57_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__58_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__58_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__58_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__58_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__58_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__58_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__58_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__57_value) as *mut crate::leanh::LeanObject,7306243862518720553 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__58: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__58_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__59_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__59: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__59_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__60_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__60: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__60_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__61_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__60_value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__61: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__61_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__62_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__62: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__62_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__63_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__63: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__64_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 101, 114, 109, 126, 126, 126, 95, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__64: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__64_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__65_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__64_value) as *mut crate::leanh::LeanObject,244005051970854221 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__65: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__65_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__66_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [126, 126, 126, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__66: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__66_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__67_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__67: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__67_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__68_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__68: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__68_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__69_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__69: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__69_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__70_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__70: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__71_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__69_value) as *mut crate::leanh::LeanObject,8767050042937596034 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__71: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__71_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__72_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [61, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__72: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__72_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__73_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 46, 116, 111, 66, 105, 116, 86, 101, 99, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__73: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__73_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__74_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__74: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__75_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__44_value) as *mut crate::leanh::LeanObject,7839396180116328695 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__75_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__75_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__69_value) as *mut crate::leanh::LeanObject,16071506607298534126 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__75: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__75_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__76_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__76: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__76_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__77_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__77_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__77_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__77_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__77_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__77_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__77_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__76_value) as *mut crate::leanh::LeanObject,13585030837571646948 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__77: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__77_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__78_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__78: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__78_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__79_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [114, 102, 108, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__79: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__79_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__80_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__80: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__81_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__79_value) as *mut crate::leanh::LeanObject,17342663138809293389 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__81: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__81_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__82_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__82: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__82_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__83_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 117, 102, 102, 105, 120, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__83: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__83_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__84_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__84_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__84_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__84_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__84_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__82_value) as *mut crate::leanh::LeanObject,7625897890118033792 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__84_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__84_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__83_value) as *mut crate::leanh::LeanObject,8715860392475343861 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__84: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__84_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__85_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 95, 97, 110, 100, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__85: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__85_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__86_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__86: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__87_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__85_value) as *mut crate::leanh::LeanObject,4445789131909237106 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__87: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__87_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__88_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 120, 112, 108, 105, 99, 105, 116, 66, 105, 110, 100, 101, 114, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__88: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__88_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__89_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__89_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__89_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__89_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__89_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__89_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__89_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__88_value) as *mut crate::leanh::LeanObject,17201320286889277233 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__89: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__89_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__90_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [98, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__90: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__90_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__91_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__91: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__92_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__90_value) as *mut crate::leanh::LeanObject,10300200614825825839 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__92: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__92_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__93_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 95, 38, 38, 38, 95, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__93: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__93_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__94_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__93_value) as *mut crate::leanh::LeanObject,12444694952413782977 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__94: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__94_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__95_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [38, 38, 38, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__95: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__95_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__96_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [98, 46, 116, 111, 66, 105, 116, 86, 101, 99, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__96: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__96_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__97_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__97: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__98_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__90_value) as *mut crate::leanh::LeanObject,10300200614825825839 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__98_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__98_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__69_value) as *mut crate::leanh::LeanObject,11947561764753763078 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__98: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__98_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__99_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 95, 111, 114, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__99: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__99_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__100_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__100: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__101_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__99_value) as *mut crate::leanh::LeanObject,9489450475637686356 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__101: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__101_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__102_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 95, 124, 124, 124, 95, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__102: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__102_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__103_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__102_value) as *mut crate::leanh::LeanObject,4575865287391746539 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__103: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__103_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__104_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [124, 124, 124, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__104: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__104_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__105_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 95, 120, 111, 114, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__105: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__105_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__106_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__106: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__107_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__105_value) as *mut crate::leanh::LeanObject,2701889046734724230 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__107: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__107_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__108_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 95, 94, 94, 94, 95, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__108: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__108_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__109_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__108_value) as *mut crate::leanh::LeanObject,4276624985753043280 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__109: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__109_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__110_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [94, 94, 94, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__110: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__110_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__111_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 95, 115, 104, 105, 102, 116, 76, 101, 102, 116, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__111: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__111_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__112_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__112: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__113_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__111_value) as *mut crate::leanh::LeanObject,18092217254651846211 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__113: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__113_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__114_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 95, 60, 60, 60, 95, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__114: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__114_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__115_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__114_value) as *mut crate::leanh::LeanObject,12923016781500733349 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__115: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__115_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__116_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [60, 60, 60, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__116: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__116_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__117_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__117: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__117_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__118_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__118_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__118_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__118_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__118_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__118_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__118_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__117_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__118: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__118_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__119_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [98, 46, 116, 111, 66, 105, 116, 86, 101, 99, 46, 115, 109, 111, 100, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__119: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__119_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__120_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__120: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__121_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 109, 111, 100, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__121: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__121_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__122_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__90_value) as *mut crate::leanh::LeanObject,10300200614825825839 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__122_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__122_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__69_value) as *mut crate::leanh::LeanObject,11947561764753763078 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__122_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__122_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__121_value) as *mut crate::leanh::LeanObject,35856969853244968 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__122: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__122_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__123_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 95, 115, 104, 105, 102, 116, 82, 105, 103, 104, 116, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__123: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__123_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__124_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__124: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__125_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__123_value) as *mut crate::leanh::LeanObject,4071013895811443549 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__125: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__125_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__126_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 95, 62, 62, 62, 95, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__126: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__126_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__127_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__126_value) as *mut crate::leanh::LeanObject,3619840007123166506 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__127: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__127_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__128_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [62, 62, 62, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__128: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__128_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__129_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [97, 46, 116, 111, 66, 105, 116, 86, 101, 99, 46, 115, 115, 104, 105, 102, 116, 82, 105, 103, 104, 116, 39, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__129: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__129_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__130_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__130: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__131_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [115, 115, 104, 105, 102, 116, 82, 105, 103, 104, 116, 39, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__131: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__131_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__132_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__44_value) as *mut crate::leanh::LeanObject,7839396180116328695 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__132_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__132_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__69_value) as *mut crate::leanh::LeanObject,16071506607298534126 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__132_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__132_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__131_value) as *mut crate::leanh::LeanObject,10658692846479171311 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__132: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__132_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__133_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 95, 97, 98, 115, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__133: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__133_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__134_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__134: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__135_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__133_value) as *mut crate::leanh::LeanObject,6514252589185591298 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__135: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__135_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__136_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [97, 46, 97, 98, 115, 46, 116, 111, 66, 105, 116, 86, 101, 99, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__136: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__136_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__137_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__137: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__138_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 98, 115, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__138: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__138_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__139_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__44_value) as *mut crate::leanh::LeanObject,7839396180116328695 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__139_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__139_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__138_value) as *mut crate::leanh::LeanObject,685682556532889679 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__139_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__139_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__69_value) as *mut crate::leanh::LeanObject,5220502750157875494 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__139: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__139_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__140_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [97, 46, 116, 111, 66, 105, 116, 86, 101, 99, 46, 97, 98, 115, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__140: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__140_value) as *mut crate::leanh::LeanObject;
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__141_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__141: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__142_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__44_value) as *mut crate::leanh::LeanObject,7839396180116328695 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__142_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__142_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__69_value) as *mut crate::leanh::LeanObject,16071506607298534126 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__142_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__142_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__138_value) as *mut crate::leanh::LeanObject,4651086619148575762 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__142: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__142_value) as *mut crate::leanh::LeanObject;
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__143_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [101, 110, 100, 0]};
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__143: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__143_value) as *mut crate::leanh::LeanObject;
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__144_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__144_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__144_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__144_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__144_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__144_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__144_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__143_value) as *mut crate::leanh::LeanObject,10057000334683702526 as *mut crate::leanh::LeanObject] };
static mut l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__144: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__144_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_644_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_644_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_680_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__26;
    v___x_681_ = l_String_toRawSubstring_x27(v___x_680_);
    return v___x_681_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__37()
-> *mut crate::leanh::LeanObject {
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_704_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__36;
    v___x_705_ = l_String_toRawSubstring_x27(v___x_704_);
    return v___x_705_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__45()
-> *mut crate::leanh::LeanObject {
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_722_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__44;
    v___x_723_ = l_String_toRawSubstring_x27(v___x_722_);
    return v___x_723_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__63()
-> *mut crate::leanh::LeanObject {
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_760_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__62;
    v___x_761_ = l_String_toRawSubstring_x27(v___x_760_);
    return v___x_761_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__70()
-> *mut crate::leanh::LeanObject {
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_769_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__69;
    v___x_770_ = l_String_toRawSubstring_x27(v___x_769_);
    return v___x_770_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__74()
-> *mut crate::leanh::LeanObject {
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_775_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__73;
    v___x_776_ = l_String_toRawSubstring_x27(v___x_775_);
    return v___x_776_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__80()
-> *mut crate::leanh::LeanObject {
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_788_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__79;
    v___x_789_ = l_String_toRawSubstring_x27(v___x_788_);
    return v___x_789_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__86()
-> *mut crate::leanh::LeanObject {
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_800_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__85;
    v___x_801_ = l_String_toRawSubstring_x27(v___x_800_);
    return v___x_801_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__91()
-> *mut crate::leanh::LeanObject {
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_811_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__90;
    v___x_812_ = l_String_toRawSubstring_x27(v___x_811_);
    return v___x_812_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__97()
-> *mut crate::leanh::LeanObject {
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_820_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__96;
    v___x_821_ = l_String_toRawSubstring_x27(v___x_820_);
    return v___x_821_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__100()
-> *mut crate::leanh::LeanObject {
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_826_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__99;
    v___x_827_ = l_String_toRawSubstring_x27(v___x_826_);
    return v___x_827_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__106()
-> *mut crate::leanh::LeanObject {
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_835_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__105;
    v___x_836_ = l_String_toRawSubstring_x27(v___x_835_);
    return v___x_836_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__112()
-> *mut crate::leanh::LeanObject {
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_844_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__111;
    v___x_845_ = l_String_toRawSubstring_x27(v___x_844_);
    return v___x_845_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__120()
-> *mut crate::leanh::LeanObject {
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_859_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__119;
    v___x_860_ = l_String_toRawSubstring_x27(v___x_859_);
    return v___x_860_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__124()
-> *mut crate::leanh::LeanObject {
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_867_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__123;
    v___x_868_ = l_String_toRawSubstring_x27(v___x_867_);
    return v___x_868_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__130()
-> *mut crate::leanh::LeanObject {
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_876_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__129;
    v___x_877_ = l_String_toRawSubstring_x27(v___x_876_);
    return v___x_877_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__134()
-> *mut crate::leanh::LeanObject {
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_884_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__133;
    v___x_885_ = l_String_toRawSubstring_x27(v___x_884_);
    return v___x_885_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__137()
-> *mut crate::leanh::LeanObject {
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_889_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__136;
    v___x_890_ = l_String_toRawSubstring_x27(v___x_889_);
    return v___x_890_;
}
pub unsafe fn _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__141()
-> *mut crate::leanh::LeanObject {
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_897_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__140;
    v___x_898_ = l_String_toRawSubstring_x27(v___x_897_);
    return v___x_898_;
}
pub unsafe fn l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1(
    mut v_x_909_: *mut crate::leanh::LeanObject,
    mut v_a_910_: *mut crate::leanh::LeanObject,
    mut v_a_911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: u8 = 0;
    v___x_912_ = l_commandDeclare__bitwise__int__theorems_____00__closed__1;
    crate::leanh::lean_inc(v_x_909_);
    v___x_913_ = l_Lean_Syntax_isOfKind(v_x_909_, v___x_912_);
    if v___x_913_ == 0 {
        let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_909_);
        v___x_914_ = crate::leanh::lean_box(1);
        v___x_915_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_915_, 0, v___x_914_);
        crate::leanh::lean_ctor_set(v___x_915_, 1, v_a_911_);
        return v___x_915_;
    } else {
        let mut v_ref_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_921_: u8 = 0;
        let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
        let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
        let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
        let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
        let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_916_ = crate::leanh::lean_ctor_get(v_a_910_, 5);
        v___x_917_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_918_ = l_Lean_Syntax_getArg(v_x_909_, v___x_917_);
        v___x_919_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_920_ = l_Lean_Syntax_getArg(v_x_909_, v___x_919_);
        crate::leanh::lean_dec(v_x_909_);
        v___x_921_ = 0;
        v___x_922_ = l_Lean_SourceInfo_fromRef(v_ref_916_, v___x_921_);
        v___x_923_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__1;
        v___x_924_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__5;
        v___x_925_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__6;
        crate::leanh::lean_inc_n(v___x_922_, 140);
        v___x_926_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_926_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_926_, 1, v___x_924_);
        crate::leanh::lean_inc_n(v___x_918_, 2);
        v___x_927_ = l_Lean_Syntax_node2(v___x_922_, v___x_925_, v___x_926_, v___x_918_);
        v___x_928_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__8;
        v___x_929_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__10;
        v___x_930_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__11), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__11_once), _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__11);
        v___x_931_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_931_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_931_, 1, v___x_923_);
        crate::leanh::lean_ctor_set(v___x_931_, 2, v___x_930_);
        v___x_932_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__14;
        v___x_933_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__15;
        v___x_934_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_934_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_934_, 1, v___x_933_);
        v___x_935_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__17;
        v___x_936_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__19;
        crate::leanh::lean_inc_ref_n(v___x_931_, 22);
        v___x_937_ = l_Lean_Syntax_node1(v___x_922_, v___x_936_, v___x_931_);
        v___x_938_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__21;
        v___x_939_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__22;
        v___x_940_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_940_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_940_, 1, v___x_938_);
        v___x_941_ = l_Lean_Syntax_node4(
            v___x_922_, v___x_939_, v___x_940_, v___x_931_, v___x_931_, v___x_931_,
        );
        crate::leanh::lean_inc(v___x_937_);
        v___x_942_ = l_Lean_Syntax_node2(v___x_922_, v___x_935_, v___x_937_, v___x_941_);
        v___x_943_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__23;
        v___x_944_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_944_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_944_, 1, v___x_943_);
        v___x_945_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__25;
        v___x_946_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__27), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__27_once), _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__27);
        v___x_947_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__28;
        v___x_948_ = crate::leanh::lean_box(0);
        v___x_949_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_949_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_949_, 1, v___x_946_);
        crate::leanh::lean_ctor_set(v___x_949_, 2, v___x_947_);
        crate::leanh::lean_ctor_set(v___x_949_, 3, v___x_948_);
        v___x_950_ = l_Lean_Syntax_node2(v___x_922_, v___x_945_, v___x_949_, v___x_931_);
        v___x_951_ = l_Lean_Syntax_node2(v___x_922_, v___x_935_, v___x_937_, v___x_950_);
        v___x_952_ =
            l_Lean_Syntax_node3(v___x_922_, v___x_923_, v___x_942_, v___x_944_, v___x_951_);
        v___x_953_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__29;
        v___x_954_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_954_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_954_, 1, v___x_953_);
        v___x_955_ =
            l_Lean_Syntax_node3(v___x_922_, v___x_932_, v___x_934_, v___x_952_, v___x_954_);
        v___x_956_ = l_Lean_Syntax_node1(v___x_922_, v___x_923_, v___x_955_);
        v___x_957_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__30;
        v___x_958_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__31;
        v___x_959_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_959_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_959_, 1, v___x_957_);
        v___x_960_ = l_Lean_Syntax_node1(v___x_922_, v___x_958_, v___x_959_);
        v___x_961_ = l_Lean_Syntax_node1(v___x_922_, v___x_923_, v___x_960_);
        v___x_962_ = l_Lean_Syntax_node7(
            v___x_922_, v___x_929_, v___x_931_, v___x_956_, v___x_931_, v___x_961_, v___x_931_,
            v___x_931_, v___x_931_,
        );
        v___x_963_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__32;
        v___x_964_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__33;
        v___x_965_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_965_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_965_, 1, v___x_963_);
        v___x_966_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__35;
        v___x_967_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__37), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__37_once), _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__37);
        v___x_968_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__38;
        v___x_969_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_969_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_969_, 1, v___x_967_);
        crate::leanh::lean_ctor_set(v___x_969_, 2, v___x_968_);
        crate::leanh::lean_ctor_set(v___x_969_, 3, v___x_948_);
        v___x_970_ = l_Lean_Syntax_node2(v___x_922_, v___x_966_, v___x_969_, v___x_931_);
        v___x_971_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__40;
        v___x_972_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__42;
        v___x_973_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__43;
        v___x_974_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_974_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_974_, 1, v___x_973_);
        v___x_975_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__45), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__45_once), _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__45);
        v___x_976_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__46;
        v___x_977_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_977_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_977_, 1, v___x_975_);
        crate::leanh::lean_ctor_set(v___x_977_, 2, v___x_976_);
        crate::leanh::lean_ctor_set(v___x_977_, 3, v___x_948_);
        crate::leanh::lean_inc_ref_n(v___x_977_, 7);
        v___x_978_ = l_Lean_Syntax_node1(v___x_922_, v___x_923_, v___x_977_);
        v___x_979_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__47;
        v___x_980_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_980_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_980_, 1, v___x_979_);
        crate::leanh::lean_inc_ref_n(v___x_980_, 7);
        v___x_981_ = l_Lean_Syntax_node2(v___x_922_, v___x_923_, v___x_980_, v___x_918_);
        v___x_982_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__48;
        v___x_983_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_983_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_983_, 1, v___x_982_);
        crate::leanh::lean_inc_n(v___x_981_, 2);
        crate::leanh::lean_inc(v___x_978_);
        v___x_984_ = l_Lean_Syntax_node4(
            v___x_922_, v___x_972_, v___x_974_, v___x_978_, v___x_981_, v___x_983_,
        );
        v___x_985_ = l_Lean_Syntax_node1(v___x_922_, v___x_923_, v___x_984_);
        v___x_986_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__50;
        v___x_987_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__52;
        v___x_988_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__54;
        v___x_989_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__56;
        v___x_990_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__58;
        v___x_991_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__59;
        v___x_992_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_992_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_992_, 1, v___x_991_);
        v___x_993_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__61;
        v___x_994_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__63), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__63_once), _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__63);
        v___x_995_ = crate::leanh::lean_box(0);
        v___x_996_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_996_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_996_, 1, v___x_994_);
        crate::leanh::lean_ctor_set(v___x_996_, 2, v___x_995_);
        crate::leanh::lean_ctor_set(v___x_996_, 3, v___x_948_);
        v___x_997_ = l_Lean_Syntax_node1(v___x_922_, v___x_993_, v___x_996_);
        crate::leanh::lean_inc_ref_n(v___x_992_, 2);
        v___x_998_ = l_Lean_Syntax_node2(v___x_922_, v___x_990_, v___x_992_, v___x_997_);
        v___x_999_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__65;
        v___x_1000_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__66;
        v___x_1001_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1001_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1001_, 1, v___x_1000_);
        crate::leanh::lean_inc_ref(v___x_1001_);
        v___x_1002_ = l_Lean_Syntax_node2(v___x_922_, v___x_999_, v___x_1001_, v___x_977_);
        v___x_1003_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__67;
        v___x_1004_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1004_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1004_, 1, v___x_1003_);
        crate::leanh::lean_inc_ref_n(v___x_1004_, 9);
        crate::leanh::lean_inc_n(v___x_998_, 7);
        v___x_1005_ =
            l_Lean_Syntax_node3(v___x_922_, v___x_989_, v___x_998_, v___x_1002_, v___x_1004_);
        v___x_1006_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__68;
        v___x_1007_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1007_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1007_, 1, v___x_1006_);
        v___x_1008_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__70), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__70_once), _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__70);
        v___x_1009_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__71;
        v___x_1010_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1010_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1010_, 1, v___x_1008_);
        crate::leanh::lean_ctor_set(v___x_1010_, 2, v___x_1009_);
        crate::leanh::lean_ctor_set(v___x_1010_, 3, v___x_948_);
        crate::leanh::lean_inc_ref_n(v___x_1010_, 5);
        crate::leanh::lean_inc_ref_n(v___x_1007_, 5);
        v___x_1011_ = l_Lean_Syntax_node3(
            v___x_922_,
            v___x_988_,
            v___x_1005_,
            v___x_1007_,
            v___x_1010_,
        );
        v___x_1012_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__72;
        v___x_1013_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1013_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1013_, 1, v___x_1012_);
        v___x_1014_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__74), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__74_once), _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__74);
        v___x_1015_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__75;
        v___x_1016_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1016_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1016_, 1, v___x_1014_);
        crate::leanh::lean_ctor_set(v___x_1016_, 2, v___x_1015_);
        crate::leanh::lean_ctor_set(v___x_1016_, 3, v___x_948_);
        crate::leanh::lean_inc_ref_n(v___x_1016_, 4);
        v___x_1017_ = l_Lean_Syntax_node2(v___x_922_, v___x_999_, v___x_1001_, v___x_1016_);
        crate::leanh::lean_inc_ref_n(v___x_1013_, 6);
        v___x_1018_ = l_Lean_Syntax_node3(
            v___x_922_,
            v___x_987_,
            v___x_1011_,
            v___x_1013_,
            v___x_1017_,
        );
        v___x_1019_ = l_Lean_Syntax_node2(v___x_922_, v___x_986_, v___x_980_, v___x_1018_);
        v___x_1020_ = l_Lean_Syntax_node2(v___x_922_, v___x_971_, v___x_985_, v___x_1019_);
        v___x_1021_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__77;
        v___x_1022_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__78;
        v___x_1023_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1023_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1023_, 1, v___x_1022_);
        v___x_1024_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__80), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__80_once), _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__80);
        v___x_1025_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__81;
        v___x_1026_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1026_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1026_, 1, v___x_1024_);
        crate::leanh::lean_ctor_set(v___x_1026_, 2, v___x_1025_);
        crate::leanh::lean_ctor_set(v___x_1026_, 3, v___x_948_);
        v___x_1027_ =
            l_Lean_Syntax_node3(v___x_922_, v___x_989_, v___x_998_, v___x_1026_, v___x_1004_);
        v___x_1028_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__84;
        v___x_1029_ = l_Lean_Syntax_node2(v___x_922_, v___x_1028_, v___x_931_, v___x_931_);
        v___x_1030_ = l_Lean_Syntax_node4(
            v___x_922_,
            v___x_1021_,
            v___x_1023_,
            v___x_1027_,
            v___x_1029_,
            v___x_931_,
        );
        crate::leanh::lean_inc_n(v___x_1030_, 6);
        crate::leanh::lean_inc_ref_n(v___x_965_, 6);
        v___x_1031_ = l_Lean_Syntax_node4(
            v___x_922_,
            v___x_964_,
            v___x_965_,
            v___x_970_,
            v___x_1020_,
            v___x_1030_,
        );
        crate::leanh::lean_inc_n(v___x_962_, 6);
        v___x_1032_ = l_Lean_Syntax_node2(v___x_922_, v___x_928_, v___x_962_, v___x_1031_);
        v___x_1033_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__86), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__86_once), _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__86);
        v___x_1034_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__87;
        v___x_1035_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1035_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1035_, 1, v___x_1033_);
        crate::leanh::lean_ctor_set(v___x_1035_, 2, v___x_1034_);
        crate::leanh::lean_ctor_set(v___x_1035_, 3, v___x_948_);
        v___x_1036_ = l_Lean_Syntax_node2(v___x_922_, v___x_966_, v___x_1035_, v___x_931_);
        v___x_1037_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__89;
        v___x_1038_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__91), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__91_once), _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__91);
        v___x_1039_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__92;
        v___x_1040_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1040_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1040_, 1, v___x_1038_);
        crate::leanh::lean_ctor_set(v___x_1040_, 2, v___x_1039_);
        crate::leanh::lean_ctor_set(v___x_1040_, 3, v___x_948_);
        crate::leanh::lean_inc_ref_n(v___x_1040_, 5);
        v___x_1041_ = l_Lean_Syntax_node2(v___x_922_, v___x_923_, v___x_977_, v___x_1040_);
        v___x_1042_ = l_Lean_Syntax_node5(
            v___x_922_,
            v___x_1037_,
            v___x_992_,
            v___x_1041_,
            v___x_981_,
            v___x_931_,
            v___x_1004_,
        );
        v___x_1043_ = l_Lean_Syntax_node1(v___x_922_, v___x_923_, v___x_1042_);
        v___x_1044_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__94;
        v___x_1045_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__95;
        v___x_1046_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1046_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1046_, 1, v___x_1045_);
        crate::leanh::lean_inc_ref(v___x_1046_);
        v___x_1047_ = l_Lean_Syntax_node3(
            v___x_922_,
            v___x_1044_,
            v___x_977_,
            v___x_1046_,
            v___x_1040_,
        );
        v___x_1048_ =
            l_Lean_Syntax_node3(v___x_922_, v___x_989_, v___x_998_, v___x_1047_, v___x_1004_);
        v___x_1049_ = l_Lean_Syntax_node3(
            v___x_922_,
            v___x_988_,
            v___x_1048_,
            v___x_1007_,
            v___x_1010_,
        );
        v___x_1050_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__97), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__97_once), _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__97);
        v___x_1051_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__98;
        v___x_1052_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1052_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1052_, 1, v___x_1050_);
        crate::leanh::lean_ctor_set(v___x_1052_, 2, v___x_1051_);
        crate::leanh::lean_ctor_set(v___x_1052_, 3, v___x_948_);
        crate::leanh::lean_inc_ref_n(v___x_1052_, 2);
        v___x_1053_ = l_Lean_Syntax_node3(
            v___x_922_,
            v___x_1044_,
            v___x_1016_,
            v___x_1046_,
            v___x_1052_,
        );
        v___x_1054_ = l_Lean_Syntax_node3(
            v___x_922_,
            v___x_987_,
            v___x_1049_,
            v___x_1013_,
            v___x_1053_,
        );
        v___x_1055_ = l_Lean_Syntax_node2(v___x_922_, v___x_986_, v___x_980_, v___x_1054_);
        crate::leanh::lean_inc_n(v___x_1043_, 4);
        v___x_1056_ = l_Lean_Syntax_node2(v___x_922_, v___x_971_, v___x_1043_, v___x_1055_);
        v___x_1057_ = l_Lean_Syntax_node4(
            v___x_922_,
            v___x_964_,
            v___x_965_,
            v___x_1036_,
            v___x_1056_,
            v___x_1030_,
        );
        v___x_1058_ = l_Lean_Syntax_node2(v___x_922_, v___x_928_, v___x_962_, v___x_1057_);
        v___x_1059_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__100), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__100_once), _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__100);
        v___x_1060_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__101;
        v___x_1061_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1061_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1061_, 1, v___x_1059_);
        crate::leanh::lean_ctor_set(v___x_1061_, 2, v___x_1060_);
        crate::leanh::lean_ctor_set(v___x_1061_, 3, v___x_948_);
        v___x_1062_ = l_Lean_Syntax_node2(v___x_922_, v___x_966_, v___x_1061_, v___x_931_);
        v___x_1063_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__103;
        v___x_1064_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__104;
        v___x_1065_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1065_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1065_, 1, v___x_1064_);
        crate::leanh::lean_inc_ref(v___x_1065_);
        v___x_1066_ = l_Lean_Syntax_node3(
            v___x_922_,
            v___x_1063_,
            v___x_977_,
            v___x_1065_,
            v___x_1040_,
        );
        v___x_1067_ =
            l_Lean_Syntax_node3(v___x_922_, v___x_989_, v___x_998_, v___x_1066_, v___x_1004_);
        v___x_1068_ = l_Lean_Syntax_node3(
            v___x_922_,
            v___x_988_,
            v___x_1067_,
            v___x_1007_,
            v___x_1010_,
        );
        v___x_1069_ = l_Lean_Syntax_node3(
            v___x_922_,
            v___x_1063_,
            v___x_1016_,
            v___x_1065_,
            v___x_1052_,
        );
        v___x_1070_ = l_Lean_Syntax_node3(
            v___x_922_,
            v___x_987_,
            v___x_1068_,
            v___x_1013_,
            v___x_1069_,
        );
        v___x_1071_ = l_Lean_Syntax_node2(v___x_922_, v___x_986_, v___x_980_, v___x_1070_);
        v___x_1072_ = l_Lean_Syntax_node2(v___x_922_, v___x_971_, v___x_1043_, v___x_1071_);
        v___x_1073_ = l_Lean_Syntax_node4(
            v___x_922_,
            v___x_964_,
            v___x_965_,
            v___x_1062_,
            v___x_1072_,
            v___x_1030_,
        );
        v___x_1074_ = l_Lean_Syntax_node2(v___x_922_, v___x_928_, v___x_962_, v___x_1073_);
        v___x_1075_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__106), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__106_once), _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__106);
        v___x_1076_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__107;
        v___x_1077_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1077_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1077_, 1, v___x_1075_);
        crate::leanh::lean_ctor_set(v___x_1077_, 2, v___x_1076_);
        crate::leanh::lean_ctor_set(v___x_1077_, 3, v___x_948_);
        v___x_1078_ = l_Lean_Syntax_node2(v___x_922_, v___x_966_, v___x_1077_, v___x_931_);
        v___x_1079_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__109;
        v___x_1080_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__110;
        v___x_1081_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1081_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1081_, 1, v___x_1080_);
        crate::leanh::lean_inc_ref(v___x_1081_);
        v___x_1082_ = l_Lean_Syntax_node3(
            v___x_922_,
            v___x_1079_,
            v___x_977_,
            v___x_1081_,
            v___x_1040_,
        );
        v___x_1083_ =
            l_Lean_Syntax_node3(v___x_922_, v___x_989_, v___x_998_, v___x_1082_, v___x_1004_);
        v___x_1084_ = l_Lean_Syntax_node3(
            v___x_922_,
            v___x_988_,
            v___x_1083_,
            v___x_1007_,
            v___x_1010_,
        );
        v___x_1085_ = l_Lean_Syntax_node3(
            v___x_922_,
            v___x_1079_,
            v___x_1016_,
            v___x_1081_,
            v___x_1052_,
        );
        v___x_1086_ = l_Lean_Syntax_node3(
            v___x_922_,
            v___x_987_,
            v___x_1084_,
            v___x_1013_,
            v___x_1085_,
        );
        v___x_1087_ = l_Lean_Syntax_node2(v___x_922_, v___x_986_, v___x_980_, v___x_1086_);
        v___x_1088_ = l_Lean_Syntax_node2(v___x_922_, v___x_971_, v___x_1043_, v___x_1087_);
        v___x_1089_ = l_Lean_Syntax_node4(
            v___x_922_,
            v___x_964_,
            v___x_965_,
            v___x_1078_,
            v___x_1088_,
            v___x_1030_,
        );
        v___x_1090_ = l_Lean_Syntax_node2(v___x_922_, v___x_928_, v___x_962_, v___x_1089_);
        v___x_1091_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__112), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__112_once), _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__112);
        v___x_1092_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__113;
        v___x_1093_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1093_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1093_, 1, v___x_1091_);
        crate::leanh::lean_ctor_set(v___x_1093_, 2, v___x_1092_);
        crate::leanh::lean_ctor_set(v___x_1093_, 3, v___x_948_);
        v___x_1094_ = l_Lean_Syntax_node2(v___x_922_, v___x_966_, v___x_1093_, v___x_931_);
        v___x_1095_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__115;
        v___x_1096_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__116;
        v___x_1097_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1097_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1097_, 1, v___x_1096_);
        crate::leanh::lean_inc_ref(v___x_1097_);
        v___x_1098_ = l_Lean_Syntax_node3(
            v___x_922_,
            v___x_1095_,
            v___x_977_,
            v___x_1097_,
            v___x_1040_,
        );
        v___x_1099_ =
            l_Lean_Syntax_node3(v___x_922_, v___x_989_, v___x_998_, v___x_1098_, v___x_1004_);
        v___x_1100_ = l_Lean_Syntax_node3(
            v___x_922_,
            v___x_988_,
            v___x_1099_,
            v___x_1007_,
            v___x_1010_,
        );
        v___x_1101_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__118;
        v___x_1102_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__120), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__120_once), _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__120);
        v___x_1103_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__122;
        v___x_1104_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1104_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1104_, 1, v___x_1102_);
        crate::leanh::lean_ctor_set(v___x_1104_, 2, v___x_1103_);
        crate::leanh::lean_ctor_set(v___x_1104_, 3, v___x_948_);
        v___x_1105_ = l_Lean_Syntax_node1(v___x_922_, v___x_923_, v___x_920_);
        v___x_1106_ = l_Lean_Syntax_node2(v___x_922_, v___x_1101_, v___x_1104_, v___x_1105_);
        v___x_1107_ =
            l_Lean_Syntax_node3(v___x_922_, v___x_989_, v___x_998_, v___x_1106_, v___x_1004_);
        crate::leanh::lean_inc(v___x_1107_);
        v___x_1108_ = l_Lean_Syntax_node3(
            v___x_922_,
            v___x_1095_,
            v___x_1016_,
            v___x_1097_,
            v___x_1107_,
        );
        v___x_1109_ = l_Lean_Syntax_node3(
            v___x_922_,
            v___x_987_,
            v___x_1100_,
            v___x_1013_,
            v___x_1108_,
        );
        v___x_1110_ = l_Lean_Syntax_node2(v___x_922_, v___x_986_, v___x_980_, v___x_1109_);
        v___x_1111_ = l_Lean_Syntax_node2(v___x_922_, v___x_971_, v___x_1043_, v___x_1110_);
        v___x_1112_ = l_Lean_Syntax_node4(
            v___x_922_,
            v___x_964_,
            v___x_965_,
            v___x_1094_,
            v___x_1111_,
            v___x_1030_,
        );
        v___x_1113_ = l_Lean_Syntax_node2(v___x_922_, v___x_928_, v___x_962_, v___x_1112_);
        v___x_1114_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__124), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__124_once), _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__124);
        v___x_1115_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__125;
        v___x_1116_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1116_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1116_, 1, v___x_1114_);
        crate::leanh::lean_ctor_set(v___x_1116_, 2, v___x_1115_);
        crate::leanh::lean_ctor_set(v___x_1116_, 3, v___x_948_);
        v___x_1117_ = l_Lean_Syntax_node2(v___x_922_, v___x_966_, v___x_1116_, v___x_931_);
        v___x_1118_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__127;
        v___x_1119_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__128;
        v___x_1120_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1120_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1120_, 1, v___x_1119_);
        v___x_1121_ = l_Lean_Syntax_node3(
            v___x_922_,
            v___x_1118_,
            v___x_977_,
            v___x_1120_,
            v___x_1040_,
        );
        v___x_1122_ =
            l_Lean_Syntax_node3(v___x_922_, v___x_989_, v___x_998_, v___x_1121_, v___x_1004_);
        v___x_1123_ = l_Lean_Syntax_node3(
            v___x_922_,
            v___x_988_,
            v___x_1122_,
            v___x_1007_,
            v___x_1010_,
        );
        v___x_1124_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__130), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__130_once), _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__130);
        v___x_1125_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__132;
        v___x_1126_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1126_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1126_, 1, v___x_1124_);
        crate::leanh::lean_ctor_set(v___x_1126_, 2, v___x_1125_);
        crate::leanh::lean_ctor_set(v___x_1126_, 3, v___x_948_);
        v___x_1127_ = l_Lean_Syntax_node1(v___x_922_, v___x_923_, v___x_1107_);
        v___x_1128_ = l_Lean_Syntax_node2(v___x_922_, v___x_1101_, v___x_1126_, v___x_1127_);
        v___x_1129_ = l_Lean_Syntax_node3(
            v___x_922_,
            v___x_987_,
            v___x_1123_,
            v___x_1013_,
            v___x_1128_,
        );
        v___x_1130_ = l_Lean_Syntax_node2(v___x_922_, v___x_986_, v___x_980_, v___x_1129_);
        v___x_1131_ = l_Lean_Syntax_node2(v___x_922_, v___x_971_, v___x_1043_, v___x_1130_);
        v___x_1132_ = l_Lean_Syntax_node4(
            v___x_922_,
            v___x_964_,
            v___x_965_,
            v___x_1117_,
            v___x_1131_,
            v___x_1030_,
        );
        v___x_1133_ = l_Lean_Syntax_node2(v___x_922_, v___x_928_, v___x_962_, v___x_1132_);
        v___x_1134_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__134), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__134_once), _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__134);
        v___x_1135_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__135;
        v___x_1136_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1136_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1136_, 1, v___x_1134_);
        crate::leanh::lean_ctor_set(v___x_1136_, 2, v___x_1135_);
        crate::leanh::lean_ctor_set(v___x_1136_, 3, v___x_948_);
        v___x_1137_ = l_Lean_Syntax_node2(v___x_922_, v___x_966_, v___x_1136_, v___x_931_);
        v___x_1138_ = l_Lean_Syntax_node5(
            v___x_922_,
            v___x_1037_,
            v___x_992_,
            v___x_978_,
            v___x_981_,
            v___x_931_,
            v___x_1004_,
        );
        v___x_1139_ = l_Lean_Syntax_node1(v___x_922_, v___x_923_, v___x_1138_);
        v___x_1140_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__137), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__137_once), _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__137);
        v___x_1141_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__139;
        v___x_1142_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1142_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1142_, 1, v___x_1140_);
        crate::leanh::lean_ctor_set(v___x_1142_, 2, v___x_1141_);
        crate::leanh::lean_ctor_set(v___x_1142_, 3, v___x_948_);
        v___x_1143_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__141), core::ptr::addr_of_mut!(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__141_once), _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__141);
        v___x_1144_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__142;
        v___x_1145_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1145_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1145_, 1, v___x_1143_);
        crate::leanh::lean_ctor_set(v___x_1145_, 2, v___x_1144_);
        crate::leanh::lean_ctor_set(v___x_1145_, 3, v___x_948_);
        v___x_1146_ = l_Lean_Syntax_node3(
            v___x_922_,
            v___x_987_,
            v___x_1142_,
            v___x_1013_,
            v___x_1145_,
        );
        v___x_1147_ = l_Lean_Syntax_node2(v___x_922_, v___x_986_, v___x_980_, v___x_1146_);
        v___x_1148_ = l_Lean_Syntax_node2(v___x_922_, v___x_971_, v___x_1139_, v___x_1147_);
        v___x_1149_ = l_Lean_Syntax_node4(
            v___x_922_,
            v___x_964_,
            v___x_965_,
            v___x_1137_,
            v___x_1148_,
            v___x_1030_,
        );
        v___x_1150_ = l_Lean_Syntax_node2(v___x_922_, v___x_928_, v___x_962_, v___x_1149_);
        v___x_1151_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__143;
        v___x_1152_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__144;
        v___x_1153_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1153_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1153_, 1, v___x_1151_);
        v___x_1154_ = l_Lean_Syntax_node2(v___x_922_, v___x_923_, v___x_918_, v___x_931_);
        v___x_1155_ = l_Lean_Syntax_node2(v___x_922_, v___x_1152_, v___x_1153_, v___x_1154_);
        v___x_1156_ = crate::leanh::lean_unsigned_to_nat(9);
        v___x_1157_ = lean_mk_empty_array_with_capacity(v___x_1156_);
        v___x_1158_ = lean_array_push(v___x_1157_, v___x_927_);
        v___x_1159_ = lean_array_push(v___x_1158_, v___x_1032_);
        v___x_1160_ = lean_array_push(v___x_1159_, v___x_1058_);
        v___x_1161_ = lean_array_push(v___x_1160_, v___x_1074_);
        v___x_1162_ = lean_array_push(v___x_1161_, v___x_1090_);
        v___x_1163_ = lean_array_push(v___x_1162_, v___x_1113_);
        v___x_1164_ = lean_array_push(v___x_1163_, v___x_1133_);
        v___x_1165_ = lean_array_push(v___x_1164_, v___x_1150_);
        v___x_1166_ = lean_array_push(v___x_1165_, v___x_1155_);
        v___x_1167_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1167_, 0, v___x_922_);
        crate::leanh::lean_ctor_set(v___x_1167_, 1, v___x_923_);
        crate::leanh::lean_ctor_set(v___x_1167_, 2, v___x_1166_);
        v___x_1168_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1168_, 0, v___x_1167_);
        crate::leanh::lean_ctor_set(v___x_1168_, 1, v_a_911_);
        return v___x_1168_;
    }
}
pub unsafe fn l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___boxed(
    mut v_x_1169_: *mut crate::leanh::LeanObject,
    mut v_a_1170_: *mut crate::leanh::LeanObject,
    mut v_a_1171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1172_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1(v_x_1169_, v_a_1170_, v_a_1171_);
    crate::leanh::lean_dec_ref(v_a_1170_);
    return v_res_1172_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_SInt_Bitwise(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_UInt_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Bitblast(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_Platform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_SInt_Bitwise(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_SInt_Bitwise(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_UInt_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_SInt_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_SInt_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Bitblast(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_SInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_System_Platform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt_Bitwise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_SInt_Bitwise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_SInt_Bitwise(builtin);
}
