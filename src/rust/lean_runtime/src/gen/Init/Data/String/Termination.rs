// Lean compiler output
// Module: Init.Data.String.Termination
// Imports: Init.Data.String.Lemmas.Splits Init.Data.String.FindPos Init.Data.Option.Lemmas Init.Omega Init.ByCases Init.Data.String.Lemmas.FindPos
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::String::FindPos::{
    initialize_Init_Data_String_FindPos, runtime_initialize_Init_Data_String_FindPos,
};
use crate::r#gen::Init::Data::String::Lemmas::FindPos::{
    initialize_Init_Data_String_Lemmas_FindPos, runtime_initialize_Init_Data_String_Lemmas_FindPos,
};
use crate::r#gen::Init::Data::String::Lemmas::Splits::{
    initialize_Init_Data_String_Lemmas_Splits, runtime_initialize_Init_Data_String_Lemmas_Splits,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node5, l_Lean_Syntax_node6,
    l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_sub, lean_string_utf8_byte_size};
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [116, 97, 99, 116, 105, 99, 68, 101, 99, 114, 101, 97, 115, 105, 110, 103, 95, 116, 114, 105, 118, 105, 97, 108, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__0_value) as *mut crate::leanh::LeanObject,5744670087858236374 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__5_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [116, 97, 99, 116, 105, 99, 95, 60, 59, 62, 95, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__5_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__5_value) as *mut crate::leanh::LeanObject,12695378809397736991 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__7_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__7_value) as *mut crate::leanh::LeanObject,8689124066155232629 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__9_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__10_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__10_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__10_value) as *mut crate::leanh::LeanObject,8504843326314613972 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__12_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__12_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__12_value) as *mut crate::leanh::LeanObject,17228437386856258271 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__14_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__14_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__16_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [119, 105, 116, 104, 82, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__16_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__16_value) as *mut crate::leanh::LeanObject,6022092293134036165 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__18_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [119, 105, 116, 104, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 104, 97, 110, 103, 101, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19_value) as *mut crate::leanh::LeanObject,16580879115603664356 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__21_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 95, 60, 95, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__22_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__21_value) as *mut crate::leanh::LeanObject,6883052497475924672 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__23_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__24_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 121, 112, 101, 65, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__24_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__23_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__24_value) as *mut crate::leanh::LeanObject,5346268661279150583 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__26_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__26_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__23_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__26_value) as *mut crate::leanh::LeanObject,7306243862518720553 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__28_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__29_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__28_value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__30_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__30_value) as *mut crate::leanh::LeanObject;
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__32_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 116, 114, 105, 110, 103, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__32_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__33_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__32_value) as *mut crate::leanh::LeanObject,3136308715950998022 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__33_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__34_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__33_value) as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__34: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__34_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__35_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__34_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__35: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__35_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__36_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__36_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__23_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__36_value) as *mut crate::leanh::LeanObject,3984140175429830279 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__38_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__38: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__38_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__39_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__39: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__39_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__40_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__40: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__40_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__23_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__40_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__42_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [83, 108, 105, 99, 101, 46, 80, 111, 115, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__42: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__42_value) as *mut crate::leanh::LeanObject;
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__44_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [83, 108, 105, 99, 101, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__44: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__44_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [80, 111, 115, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__44_value) as *mut crate::leanh::LeanObject,8187769831118341293 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value) as *mut crate::leanh::LeanObject,16202482610869712088 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__47_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__32_value) as *mut crate::leanh::LeanObject,3136308715950998022 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__47_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__47_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__44_value) as *mut crate::leanh::LeanObject,5019532346282914388 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__47_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__47_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value) as *mut crate::leanh::LeanObject,14099492201261393173 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__47: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__47_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__48_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__47_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__48: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__48_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__49_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__47_value) as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__49: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__49_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__50_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__49_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__50: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__50_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__51_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__48_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__50_value) as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__51: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__51_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__52_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__52: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__52_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__53_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [60, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__53: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__53_value) as *mut crate::leanh::LeanObject;
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55_value) as *mut crate::leanh::LeanObject,12783917532758215986 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__57_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__57: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__57_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__57_value) as *mut crate::leanh::LeanObject,3488656302031949961 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__59_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__59: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__59_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__60_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 105, 109, 112, 76, 101, 109, 109, 97, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__60: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__60_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__60_value) as *mut crate::leanh::LeanObject,7383208167966365478 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__62_value: crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [83, 108, 105, 99, 101, 46, 80, 111, 115, 46, 101, 113, 95, 110, 101, 120, 116, 95, 111, 102, 95, 110, 101, 120, 116, 63, 95, 101, 113, 95, 115, 111, 109, 101, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__62: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__62_value) as *mut crate::leanh::LeanObject;
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__63_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__63: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__64_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [101, 113, 95, 110, 101, 120, 116, 95, 111, 102, 95, 110, 101, 120, 116, 63, 95, 101, 113, 95, 115, 111, 109, 101, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__64: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__64_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__65_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__44_value) as *mut crate::leanh::LeanObject,8187769831118341293 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__65_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__65_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value) as *mut crate::leanh::LeanObject,16202482610869712088 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__65_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__65_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__64_value) as *mut crate::leanh::LeanObject,13679438009283193378 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__65: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__65_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__66_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__32_value) as *mut crate::leanh::LeanObject,3136308715950998022 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__66_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__66_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__44_value) as *mut crate::leanh::LeanObject,5019532346282914388 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__66_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__66_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value) as *mut crate::leanh::LeanObject,14099492201261393173 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__66_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__66_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__64_value) as *mut crate::leanh::LeanObject,2388340585233324067 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__66: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__66_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__67_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__66_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__67: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__67_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__68_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__67_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__68: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__68_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__23_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__7_value) as *mut crate::leanh::LeanObject,7932075773091973500 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__70_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 121, 84, 97, 99, 116, 105, 99, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__70: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__70_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__23_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__70_value) as *mut crate::leanh::LeanObject,16173796135615239867 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__72_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [98, 121, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__72: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__72_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 115, 115, 117, 109, 112, 116, 105, 111, 110, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73_value) as *mut crate::leanh::LeanObject,16687334436616221424 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__75_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__75: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__75_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__76_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__76: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__76_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__77_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [60, 59, 62, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__77: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__77_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 111, 110, 101, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78_value) as *mut crate::leanh::LeanObject,8876691400619696497 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__0_value: crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [83, 108, 105, 99, 101, 46, 80, 111, 115, 46, 101, 113, 95, 112, 114, 101, 118, 95, 111, 102, 95, 112, 114, 101, 118, 63, 95, 101, 113, 95, 115, 111, 109, 101, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__2_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [101, 113, 95, 112, 114, 101, 118, 95, 111, 102, 95, 112, 114, 101, 118, 63, 95, 101, 113, 95, 115, 111, 109, 101, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__2_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__44_value) as *mut crate::leanh::LeanObject,8187769831118341293 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value) as *mut crate::leanh::LeanObject,16202482610869712088 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__2_value) as *mut crate::leanh::LeanObject,3093888679394696540 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__3_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__32_value) as *mut crate::leanh::LeanObject,3136308715950998022 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__44_value) as *mut crate::leanh::LeanObject,5019532346282914388 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value) as *mut crate::leanh::LeanObject,14099492201261393173 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__2_value) as *mut crate::leanh::LeanObject,14466701744559606069 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__5_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [83, 116, 114, 105, 110, 103, 46, 80, 111, 115, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__32_value) as *mut crate::leanh::LeanObject,3136308715950998022 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value) as *mut crate::leanh::LeanObject,12573450411011270351 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__2_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__4_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__7_value: crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [80, 111, 115, 46, 101, 113, 95, 110, 101, 120, 116, 95, 111, 102, 95, 110, 101, 120, 116, 63, 95, 101, 113, 95, 115, 111, 109, 101, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value) as *mut crate::leanh::LeanObject,3418672936842095366 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__64_value) as *mut crate::leanh::LeanObject,11936469576340500500 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__9_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__32_value) as *mut crate::leanh::LeanObject,3136308715950998022 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value) as *mut crate::leanh::LeanObject,12573450411011270351 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__10_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__64_value) as *mut crate::leanh::LeanObject,18029240850150918033 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__12_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__11_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__0_value: crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [80, 111, 115, 46, 101, 113, 95, 112, 114, 101, 118, 95, 111, 102, 95, 112, 114, 101, 118, 63, 95, 101, 113, 95, 115, 111, 109, 101, 0]};
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value) as *mut crate::leanh::LeanObject,3418672936842095366 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__2_value) as *mut crate::leanh::LeanObject,15700574850277155354 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__2_value) as *mut crate::leanh::LeanObject;
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__32_value) as *mut crate::leanh::LeanObject,3136308715950998022 as *mut crate::leanh::LeanObject] };
static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__45_value) as *mut crate::leanh::LeanObject,12573450411011270351 as *mut crate::leanh::LeanObject] };
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__2_value) as *mut crate::leanh::LeanObject,1019701262852998935 as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__3_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__5_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_String_Slice_Pos_remainingBytes(
    mut v_s_765_: *mut crate::leanh::LeanObject,
    mut v_p_766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_767_ = crate::leanh::lean_ctor_get(v_s_765_, 1);
    v_endExclusive_768_ = crate::leanh::lean_ctor_get(v_s_765_, 2);
    v___x_769_ = lean_nat_sub(v_endExclusive_768_, v_startInclusive_767_);
    v___x_770_ = lean_nat_sub(v___x_769_, v_p_766_);
    crate::leanh::lean_dec(v___x_769_);
    return v___x_770_;
}
pub unsafe fn l_String_Slice_Pos_remainingBytes___boxed(
    mut v_s_771_: *mut crate::leanh::LeanObject,
    mut v_p_772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_773_ = l_String_Slice_Pos_remainingBytes(v_s_771_, v_p_772_);
    crate::leanh::lean_dec(v_p_772_);
    crate::leanh::lean_dec_ref(v_s_771_);
    return v_res_773_;
}
pub unsafe fn l_String_Slice_Pos_instWellFoundedRelation(
    mut v_s_774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_775_ = crate::leanh::lean_box(0);
    return v___x_775_;
}
pub unsafe fn l_String_Slice_Pos_instWellFoundedRelation___boxed(
    mut v_s_776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_777_ = l_String_Slice_Pos_instWellFoundedRelation(v_s_776_);
    crate::leanh::lean_dec_ref(v_s_776_);
    return v_res_777_;
}
pub unsafe fn l_String_Slice_Pos_down___redArg(
    mut v_p_778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_p_778_);
    return v_p_778_;
}
pub unsafe fn l_String_Slice_Pos_down___redArg___boxed(
    mut v_p_779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_780_ = l_String_Slice_Pos_down___redArg(v_p_779_);
    crate::leanh::lean_dec(v_p_779_);
    return v_res_780_;
}
pub unsafe fn l_String_Slice_Pos_down(
    mut v_s_781_: *mut crate::leanh::LeanObject,
    mut v_p_782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_p_782_);
    return v_p_782_;
}
pub unsafe fn l_String_Slice_Pos_down___boxed(
    mut v_s_783_: *mut crate::leanh::LeanObject,
    mut v_p_784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_785_ = l_String_Slice_Pos_down(v_s_783_, v_p_784_);
    crate::leanh::lean_dec(v_p_784_);
    crate::leanh::lean_dec_ref(v_s_783_);
    return v_res_785_;
}
pub unsafe fn l_String_Slice_Pos_instWellFoundedRelationDown(
    mut v_s_786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_787_ = crate::leanh::lean_box(0);
    return v___x_787_;
}
pub unsafe fn l_String_Slice_Pos_instWellFoundedRelationDown___boxed(
    mut v_s_788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_789_ = l_String_Slice_Pos_instWellFoundedRelationDown(v_s_788_);
    crate::leanh::lean_dec_ref(v_s_788_);
    return v_res_789_;
}
pub unsafe fn l_String_Pos_remainingBytes(
    mut v_s_790_: *mut crate::leanh::LeanObject,
    mut v_p_791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_792_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_793_ = lean_string_utf8_byte_size(v_s_790_);
    v___x_794_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_794_, 0, v_s_790_);
    crate::leanh::lean_ctor_set(v___x_794_, 1, v___x_792_);
    crate::leanh::lean_ctor_set(v___x_794_, 2, v___x_793_);
    v___x_795_ = l_String_Slice_Pos_remainingBytes(v___x_794_, v_p_791_);
    crate::leanh::lean_dec_ref_known(v___x_794_, 3);
    return v___x_795_;
}
pub unsafe fn l_String_Pos_remainingBytes___boxed(
    mut v_s_796_: *mut crate::leanh::LeanObject,
    mut v_p_797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_798_ = l_String_Pos_remainingBytes(v_s_796_, v_p_797_);
    crate::leanh::lean_dec(v_p_797_);
    return v_res_798_;
}
pub unsafe fn l_String_Pos_instWellFoundedRelation(
    mut v_s_799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_800_ = crate::leanh::lean_box(0);
    return v___x_800_;
}
pub unsafe fn l_String_Pos_instWellFoundedRelation___boxed(
    mut v_s_801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_802_ = l_String_Pos_instWellFoundedRelation(v_s_801_);
    crate::leanh::lean_dec_ref(v_s_801_);
    return v_res_802_;
}
pub unsafe fn l_String_Pos_down___redArg(
    mut v_p_803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_p_803_);
    return v_p_803_;
}
pub unsafe fn l_String_Pos_down___redArg___boxed(
    mut v_p_804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_805_ = l_String_Pos_down___redArg(v_p_804_);
    crate::leanh::lean_dec(v_p_804_);
    return v_res_805_;
}
pub unsafe fn l_String_Pos_down(
    mut v_s_806_: *mut crate::leanh::LeanObject,
    mut v_p_807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_p_807_);
    return v_p_807_;
}
pub unsafe fn l_String_Pos_down___boxed(
    mut v_s_808_: *mut crate::leanh::LeanObject,
    mut v_p_809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_810_ = l_String_Pos_down(v_s_808_, v_p_809_);
    crate::leanh::lean_dec(v_p_809_);
    crate::leanh::lean_dec_ref(v_s_808_);
    return v_res_810_;
}
pub unsafe fn l_String_Pos_instWellFoundedRelationDown(
    mut v_s_811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_812_ = crate::leanh::lean_box(0);
    return v___x_812_;
}
pub unsafe fn l_String_Pos_instWellFoundedRelationDown___boxed(
    mut v_s_813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_814_ = l_String_Pos_instWellFoundedRelationDown(v_s_813_);
    crate::leanh::lean_dec_ref(v_s_813_);
    return v_res_814_;
}
pub unsafe fn _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_882_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__30;
    v___x_883_ = l_String_toRawSubstring_x27(v___x_882_);
    return v___x_883_;
}
pub unsafe fn _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43()
-> *mut crate::leanh::LeanObject {
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_907_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__42;
    v___x_908_ = l_String_toRawSubstring_x27(v___x_907_);
    return v___x_908_;
}
pub unsafe fn _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54()
-> *mut crate::leanh::LeanObject {
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_931_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_931_;
}
pub unsafe fn _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__63()
-> *mut crate::leanh::LeanObject {
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_952_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__62;
    v___x_953_ = l_String_toRawSubstring_x27(v___x_952_);
    return v___x_953_;
}
pub unsafe fn l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1(
    mut v_x_997_: *mut crate::leanh::LeanObject,
    mut v_a_998_: *mut crate::leanh::LeanObject,
    mut v_a_999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: u8 = 0;
    v___x_1000_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__1;
    v___x_1001_ = l_Lean_Syntax_isOfKind(v_x_997_, v___x_1000_);
    if v___x_1001_ == 0 {
        let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1002_ = crate::leanh::lean_box(1);
        v___x_1003_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1003_, 0, v___x_1002_);
        crate::leanh::lean_ctor_set(v___x_1003_, 1, v_a_999_);
        return v___x_1003_;
    } else {
        let mut v_quotContext_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1007_: u8 = 0;
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
        v_quotContext_1004_ = crate::leanh::lean_ctor_get(v_a_998_, 1);
        v_currMacroScope_1005_ = crate::leanh::lean_ctor_get(v_a_998_, 2);
        v_ref_1006_ = crate::leanh::lean_ctor_get(v_a_998_, 5);
        v___x_1007_ = 0;
        v___x_1008_ = l_Lean_SourceInfo_fromRef(v_ref_1006_, v___x_1007_);
        v___x_1009_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6;
        v___x_1010_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8;
        v___x_1011_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__9;
        crate::leanh::lean_inc_n(v___x_1008_, 50);
        v___x_1012_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1012_, 0, v___x_1008_);
        crate::leanh::lean_ctor_set(v___x_1012_, 1, v___x_1011_);
        v___x_1013_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11;
        v___x_1014_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13;
        v___x_1015_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__15;
        v___x_1016_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17;
        v___x_1017_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__18;
        v___x_1018_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1018_, 0, v___x_1008_);
        crate::leanh::lean_ctor_set(v___x_1018_, 1, v___x_1017_);
        v___x_1019_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19;
        v___x_1020_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20;
        v___x_1021_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1021_, 0, v___x_1008_);
        crate::leanh::lean_ctor_set(v___x_1021_, 1, v___x_1019_);
        v___x_1022_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__22;
        v___x_1023_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25;
        v___x_1024_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27;
        v___x_1025_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__29;
        v___x_1026_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31), core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31_once), _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31);
        v___x_1027_ = crate::leanh::lean_box(0);
        crate::leanh::lean_inc_n(v_currMacroScope_1005_, 3);
        crate::leanh::lean_inc_n(v_quotContext_1004_, 3);
        v___x_1028_ =
            l_Lean_addMacroScope(v_quotContext_1004_, v___x_1027_, v_currMacroScope_1005_);
        v___x_1029_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__35;
        v___x_1030_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1030_, 0, v___x_1008_);
        crate::leanh::lean_ctor_set(v___x_1030_, 1, v___x_1026_);
        crate::leanh::lean_ctor_set(v___x_1030_, 2, v___x_1028_);
        crate::leanh::lean_ctor_set(v___x_1030_, 3, v___x_1029_);
        v___x_1031_ = l_Lean_Syntax_node1(v___x_1008_, v___x_1025_, v___x_1030_);
        crate::leanh::lean_inc_ref(v___x_1012_);
        v___x_1032_ = l_Lean_Syntax_node2(v___x_1008_, v___x_1024_, v___x_1012_, v___x_1031_);
        v___x_1033_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37;
        v___x_1034_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__38;
        v___x_1035_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1035_, 0, v___x_1008_);
        crate::leanh::lean_ctor_set(v___x_1035_, 1, v___x_1034_);
        v___x_1036_ = l_Lean_Syntax_node1(v___x_1008_, v___x_1033_, v___x_1035_);
        v___x_1037_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__39;
        v___x_1038_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1038_, 0, v___x_1008_);
        crate::leanh::lean_ctor_set(v___x_1038_, 1, v___x_1037_);
        v___x_1039_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41;
        v___x_1040_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43), core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43_once), _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43);
        v___x_1041_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46;
        v___x_1042_ =
            l_Lean_addMacroScope(v_quotContext_1004_, v___x_1041_, v_currMacroScope_1005_);
        v___x_1043_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__51;
        v___x_1044_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1044_, 0, v___x_1008_);
        crate::leanh::lean_ctor_set(v___x_1044_, 1, v___x_1040_);
        crate::leanh::lean_ctor_set(v___x_1044_, 2, v___x_1042_);
        crate::leanh::lean_ctor_set(v___x_1044_, 3, v___x_1043_);
        crate::leanh::lean_inc_n(v___x_1036_, 2);
        v___x_1045_ = l_Lean_Syntax_node1(v___x_1008_, v___x_1015_, v___x_1036_);
        v___x_1046_ = l_Lean_Syntax_node2(v___x_1008_, v___x_1039_, v___x_1044_, v___x_1045_);
        v___x_1047_ = l_Lean_Syntax_node1(v___x_1008_, v___x_1015_, v___x_1046_);
        v___x_1048_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__52;
        v___x_1049_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1049_, 0, v___x_1008_);
        crate::leanh::lean_ctor_set(v___x_1049_, 1, v___x_1048_);
        crate::leanh::lean_inc_ref_n(v___x_1049_, 2);
        crate::leanh::lean_inc(v___x_1032_);
        v___x_1050_ = l_Lean_Syntax_node5(
            v___x_1008_,
            v___x_1023_,
            v___x_1032_,
            v___x_1036_,
            v___x_1038_,
            v___x_1047_,
            v___x_1049_,
        );
        v___x_1051_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__53;
        v___x_1052_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1052_, 0, v___x_1008_);
        crate::leanh::lean_ctor_set(v___x_1052_, 1, v___x_1051_);
        v___x_1053_ = l_Lean_Syntax_node3(
            v___x_1008_,
            v___x_1022_,
            v___x_1050_,
            v___x_1052_,
            v___x_1036_,
        );
        v___x_1054_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54), core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54_once), _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54);
        v___x_1055_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1055_, 0, v___x_1008_);
        crate::leanh::lean_ctor_set(v___x_1055_, 1, v___x_1015_);
        crate::leanh::lean_ctor_set(v___x_1055_, 2, v___x_1054_);
        crate::leanh::lean_inc_ref_n(v___x_1055_, 7);
        v___x_1056_ = l_Lean_Syntax_node3(
            v___x_1008_,
            v___x_1020_,
            v___x_1021_,
            v___x_1053_,
            v___x_1055_,
        );
        v___x_1057_ = l_Lean_Syntax_node1(v___x_1008_, v___x_1015_, v___x_1056_);
        v___x_1058_ = l_Lean_Syntax_node1(v___x_1008_, v___x_1014_, v___x_1057_);
        v___x_1059_ = l_Lean_Syntax_node1(v___x_1008_, v___x_1013_, v___x_1058_);
        v___x_1060_ = l_Lean_Syntax_node2(v___x_1008_, v___x_1016_, v___x_1018_, v___x_1059_);
        v___x_1061_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55;
        v___x_1062_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56;
        v___x_1063_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1063_, 0, v___x_1008_);
        crate::leanh::lean_ctor_set(v___x_1063_, 1, v___x_1061_);
        v___x_1064_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58;
        v___x_1065_ = l_Lean_Syntax_node1(v___x_1008_, v___x_1064_, v___x_1055_);
        v___x_1066_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__59;
        v___x_1067_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1067_, 0, v___x_1008_);
        crate::leanh::lean_ctor_set(v___x_1067_, 1, v___x_1066_);
        v___x_1068_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61;
        v___x_1069_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__63), core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__63_once), _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__63);
        v___x_1070_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__65;
        v___x_1071_ =
            l_Lean_addMacroScope(v_quotContext_1004_, v___x_1070_, v_currMacroScope_1005_);
        v___x_1072_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__68;
        v___x_1073_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1073_, 0, v___x_1008_);
        crate::leanh::lean_ctor_set(v___x_1073_, 1, v___x_1069_);
        crate::leanh::lean_ctor_set(v___x_1073_, 2, v___x_1071_);
        crate::leanh::lean_ctor_set(v___x_1073_, 3, v___x_1072_);
        v___x_1074_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69;
        v___x_1075_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71;
        v___x_1076_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__72;
        v___x_1077_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1077_, 0, v___x_1008_);
        crate::leanh::lean_ctor_set(v___x_1077_, 1, v___x_1076_);
        v___x_1078_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73;
        v___x_1079_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74;
        v___x_1080_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1080_, 0, v___x_1008_);
        crate::leanh::lean_ctor_set(v___x_1080_, 1, v___x_1078_);
        v___x_1081_ = l_Lean_Syntax_node1(v___x_1008_, v___x_1079_, v___x_1080_);
        v___x_1082_ = l_Lean_Syntax_node1(v___x_1008_, v___x_1015_, v___x_1081_);
        v___x_1083_ = l_Lean_Syntax_node1(v___x_1008_, v___x_1014_, v___x_1082_);
        v___x_1084_ = l_Lean_Syntax_node1(v___x_1008_, v___x_1013_, v___x_1083_);
        v___x_1085_ = l_Lean_Syntax_node2(v___x_1008_, v___x_1075_, v___x_1077_, v___x_1084_);
        v___x_1086_ = l_Lean_Syntax_node3(
            v___x_1008_,
            v___x_1074_,
            v___x_1032_,
            v___x_1085_,
            v___x_1049_,
        );
        v___x_1087_ = l_Lean_Syntax_node1(v___x_1008_, v___x_1015_, v___x_1086_);
        v___x_1088_ = l_Lean_Syntax_node2(v___x_1008_, v___x_1039_, v___x_1073_, v___x_1087_);
        v___x_1089_ = l_Lean_Syntax_node3(
            v___x_1008_,
            v___x_1068_,
            v___x_1055_,
            v___x_1055_,
            v___x_1088_,
        );
        v___x_1090_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__75;
        v___x_1091_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1091_, 0, v___x_1008_);
        crate::leanh::lean_ctor_set(v___x_1091_, 1, v___x_1090_);
        v___x_1092_ = l_Lean_Syntax_node2(v___x_1008_, v___x_1015_, v___x_1089_, v___x_1091_);
        v___x_1093_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__76;
        v___x_1094_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1094_, 0, v___x_1008_);
        crate::leanh::lean_ctor_set(v___x_1094_, 1, v___x_1093_);
        v___x_1095_ = l_Lean_Syntax_node3(
            v___x_1008_,
            v___x_1015_,
            v___x_1067_,
            v___x_1092_,
            v___x_1094_,
        );
        v___x_1096_ = l_Lean_Syntax_node6(
            v___x_1008_,
            v___x_1062_,
            v___x_1063_,
            v___x_1065_,
            v___x_1055_,
            v___x_1055_,
            v___x_1095_,
            v___x_1055_,
        );
        v___x_1097_ = l_Lean_Syntax_node3(
            v___x_1008_,
            v___x_1015_,
            v___x_1060_,
            v___x_1055_,
            v___x_1096_,
        );
        v___x_1098_ = l_Lean_Syntax_node1(v___x_1008_, v___x_1014_, v___x_1097_);
        v___x_1099_ = l_Lean_Syntax_node1(v___x_1008_, v___x_1013_, v___x_1098_);
        v___x_1100_ = l_Lean_Syntax_node3(
            v___x_1008_,
            v___x_1010_,
            v___x_1012_,
            v___x_1099_,
            v___x_1049_,
        );
        v___x_1101_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__77;
        v___x_1102_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1102_, 0, v___x_1008_);
        crate::leanh::lean_ctor_set(v___x_1102_, 1, v___x_1101_);
        v___x_1103_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78;
        v___x_1104_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79;
        v___x_1105_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1105_, 0, v___x_1008_);
        crate::leanh::lean_ctor_set(v___x_1105_, 1, v___x_1103_);
        v___x_1106_ = l_Lean_Syntax_node1(v___x_1008_, v___x_1104_, v___x_1105_);
        v___x_1107_ = l_Lean_Syntax_node3(
            v___x_1008_,
            v___x_1009_,
            v___x_1100_,
            v___x_1102_,
            v___x_1106_,
        );
        v___x_1108_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1108_, 0, v___x_1107_);
        crate::leanh::lean_ctor_set(v___x_1108_, 1, v_a_999_);
        return v___x_1108_;
    }
}
pub unsafe fn l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___boxed(
    mut v_x_1109_: *mut crate::leanh::LeanObject,
    mut v_a_1110_: *mut crate::leanh::LeanObject,
    mut v_a_1111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1112_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1(v_x_1109_, v_a_1110_, v_a_1111_);
    crate::leanh::lean_dec_ref(v_a_1110_);
    return v_res_1112_;
}
pub unsafe fn _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1114_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__0;
    v___x_1115_ = l_String_toRawSubstring_x27(v___x_1114_);
    return v___x_1115_;
}
pub unsafe fn l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2(
    mut v_x_1132_: *mut crate::leanh::LeanObject,
    mut v_a_1133_: *mut crate::leanh::LeanObject,
    mut v_a_1134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: u8 = 0;
    v___x_1135_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__1;
    v___x_1136_ = l_Lean_Syntax_isOfKind(v_x_1132_, v___x_1135_);
    if v___x_1136_ == 0 {
        let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1137_ = crate::leanh::lean_box(1);
        v___x_1138_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1138_, 0, v___x_1137_);
        crate::leanh::lean_ctor_set(v___x_1138_, 1, v_a_1134_);
        return v___x_1138_;
    } else {
        let mut v_quotContext_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1142_: u8 = 0;
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
        let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1139_ = crate::leanh::lean_ctor_get(v_a_1133_, 1);
        v_currMacroScope_1140_ = crate::leanh::lean_ctor_get(v_a_1133_, 2);
        v_ref_1141_ = crate::leanh::lean_ctor_get(v_a_1133_, 5);
        v___x_1142_ = 0;
        v___x_1143_ = l_Lean_SourceInfo_fromRef(v_ref_1141_, v___x_1142_);
        v___x_1144_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6;
        v___x_1145_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8;
        v___x_1146_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__9;
        crate::leanh::lean_inc_n(v___x_1143_, 50);
        v___x_1147_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1147_, 0, v___x_1143_);
        crate::leanh::lean_ctor_set(v___x_1147_, 1, v___x_1146_);
        v___x_1148_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11;
        v___x_1149_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13;
        v___x_1150_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__15;
        v___x_1151_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17;
        v___x_1152_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__18;
        v___x_1153_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1153_, 0, v___x_1143_);
        crate::leanh::lean_ctor_set(v___x_1153_, 1, v___x_1152_);
        v___x_1154_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19;
        v___x_1155_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20;
        v___x_1156_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1156_, 0, v___x_1143_);
        crate::leanh::lean_ctor_set(v___x_1156_, 1, v___x_1154_);
        v___x_1157_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__22;
        v___x_1158_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25;
        v___x_1159_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27;
        v___x_1160_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__29;
        v___x_1161_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31), core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31_once), _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31);
        v___x_1162_ = crate::leanh::lean_box(0);
        crate::leanh::lean_inc_n(v_currMacroScope_1140_, 3);
        crate::leanh::lean_inc_n(v_quotContext_1139_, 3);
        v___x_1163_ =
            l_Lean_addMacroScope(v_quotContext_1139_, v___x_1162_, v_currMacroScope_1140_);
        v___x_1164_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__35;
        v___x_1165_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1165_, 0, v___x_1143_);
        crate::leanh::lean_ctor_set(v___x_1165_, 1, v___x_1161_);
        crate::leanh::lean_ctor_set(v___x_1165_, 2, v___x_1163_);
        crate::leanh::lean_ctor_set(v___x_1165_, 3, v___x_1164_);
        v___x_1166_ = l_Lean_Syntax_node1(v___x_1143_, v___x_1160_, v___x_1165_);
        crate::leanh::lean_inc_ref(v___x_1147_);
        v___x_1167_ = l_Lean_Syntax_node2(v___x_1143_, v___x_1159_, v___x_1147_, v___x_1166_);
        v___x_1168_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37;
        v___x_1169_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__38;
        v___x_1170_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1170_, 0, v___x_1143_);
        crate::leanh::lean_ctor_set(v___x_1170_, 1, v___x_1169_);
        v___x_1171_ = l_Lean_Syntax_node1(v___x_1143_, v___x_1168_, v___x_1170_);
        v___x_1172_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__39;
        v___x_1173_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1173_, 0, v___x_1143_);
        crate::leanh::lean_ctor_set(v___x_1173_, 1, v___x_1172_);
        v___x_1174_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41;
        v___x_1175_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43), core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43_once), _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__43);
        v___x_1176_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__46;
        v___x_1177_ =
            l_Lean_addMacroScope(v_quotContext_1139_, v___x_1176_, v_currMacroScope_1140_);
        v___x_1178_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__51;
        v___x_1179_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1179_, 0, v___x_1143_);
        crate::leanh::lean_ctor_set(v___x_1179_, 1, v___x_1175_);
        crate::leanh::lean_ctor_set(v___x_1179_, 2, v___x_1177_);
        crate::leanh::lean_ctor_set(v___x_1179_, 3, v___x_1178_);
        crate::leanh::lean_inc_n(v___x_1171_, 2);
        v___x_1180_ = l_Lean_Syntax_node1(v___x_1143_, v___x_1150_, v___x_1171_);
        v___x_1181_ = l_Lean_Syntax_node2(v___x_1143_, v___x_1174_, v___x_1179_, v___x_1180_);
        v___x_1182_ = l_Lean_Syntax_node1(v___x_1143_, v___x_1150_, v___x_1181_);
        v___x_1183_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__52;
        v___x_1184_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1184_, 0, v___x_1143_);
        crate::leanh::lean_ctor_set(v___x_1184_, 1, v___x_1183_);
        crate::leanh::lean_inc_ref_n(v___x_1184_, 2);
        crate::leanh::lean_inc(v___x_1167_);
        v___x_1185_ = l_Lean_Syntax_node5(
            v___x_1143_,
            v___x_1158_,
            v___x_1167_,
            v___x_1171_,
            v___x_1173_,
            v___x_1182_,
            v___x_1184_,
        );
        v___x_1186_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__53;
        v___x_1187_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1187_, 0, v___x_1143_);
        crate::leanh::lean_ctor_set(v___x_1187_, 1, v___x_1186_);
        v___x_1188_ = l_Lean_Syntax_node3(
            v___x_1143_,
            v___x_1157_,
            v___x_1185_,
            v___x_1187_,
            v___x_1171_,
        );
        v___x_1189_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54), core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54_once), _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54);
        v___x_1190_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1190_, 0, v___x_1143_);
        crate::leanh::lean_ctor_set(v___x_1190_, 1, v___x_1150_);
        crate::leanh::lean_ctor_set(v___x_1190_, 2, v___x_1189_);
        crate::leanh::lean_inc_ref_n(v___x_1190_, 7);
        v___x_1191_ = l_Lean_Syntax_node3(
            v___x_1143_,
            v___x_1155_,
            v___x_1156_,
            v___x_1188_,
            v___x_1190_,
        );
        v___x_1192_ = l_Lean_Syntax_node1(v___x_1143_, v___x_1150_, v___x_1191_);
        v___x_1193_ = l_Lean_Syntax_node1(v___x_1143_, v___x_1149_, v___x_1192_);
        v___x_1194_ = l_Lean_Syntax_node1(v___x_1143_, v___x_1148_, v___x_1193_);
        v___x_1195_ = l_Lean_Syntax_node2(v___x_1143_, v___x_1151_, v___x_1153_, v___x_1194_);
        v___x_1196_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55;
        v___x_1197_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56;
        v___x_1198_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1198_, 0, v___x_1143_);
        crate::leanh::lean_ctor_set(v___x_1198_, 1, v___x_1196_);
        v___x_1199_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58;
        v___x_1200_ = l_Lean_Syntax_node1(v___x_1143_, v___x_1199_, v___x_1190_);
        v___x_1201_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__59;
        v___x_1202_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1202_, 0, v___x_1143_);
        crate::leanh::lean_ctor_set(v___x_1202_, 1, v___x_1201_);
        v___x_1203_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61;
        v___x_1204_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__1), core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__1_once), _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__1);
        v___x_1205_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__3;
        v___x_1206_ =
            l_Lean_addMacroScope(v_quotContext_1139_, v___x_1205_, v_currMacroScope_1140_);
        v___x_1207_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___closed__6;
        v___x_1208_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1208_, 0, v___x_1143_);
        crate::leanh::lean_ctor_set(v___x_1208_, 1, v___x_1204_);
        crate::leanh::lean_ctor_set(v___x_1208_, 2, v___x_1206_);
        crate::leanh::lean_ctor_set(v___x_1208_, 3, v___x_1207_);
        v___x_1209_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69;
        v___x_1210_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71;
        v___x_1211_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__72;
        v___x_1212_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1212_, 0, v___x_1143_);
        crate::leanh::lean_ctor_set(v___x_1212_, 1, v___x_1211_);
        v___x_1213_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73;
        v___x_1214_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74;
        v___x_1215_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1215_, 0, v___x_1143_);
        crate::leanh::lean_ctor_set(v___x_1215_, 1, v___x_1213_);
        v___x_1216_ = l_Lean_Syntax_node1(v___x_1143_, v___x_1214_, v___x_1215_);
        v___x_1217_ = l_Lean_Syntax_node1(v___x_1143_, v___x_1150_, v___x_1216_);
        v___x_1218_ = l_Lean_Syntax_node1(v___x_1143_, v___x_1149_, v___x_1217_);
        v___x_1219_ = l_Lean_Syntax_node1(v___x_1143_, v___x_1148_, v___x_1218_);
        v___x_1220_ = l_Lean_Syntax_node2(v___x_1143_, v___x_1210_, v___x_1212_, v___x_1219_);
        v___x_1221_ = l_Lean_Syntax_node3(
            v___x_1143_,
            v___x_1209_,
            v___x_1167_,
            v___x_1220_,
            v___x_1184_,
        );
        v___x_1222_ = l_Lean_Syntax_node1(v___x_1143_, v___x_1150_, v___x_1221_);
        v___x_1223_ = l_Lean_Syntax_node2(v___x_1143_, v___x_1174_, v___x_1208_, v___x_1222_);
        v___x_1224_ = l_Lean_Syntax_node3(
            v___x_1143_,
            v___x_1203_,
            v___x_1190_,
            v___x_1190_,
            v___x_1223_,
        );
        v___x_1225_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__75;
        v___x_1226_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1226_, 0, v___x_1143_);
        crate::leanh::lean_ctor_set(v___x_1226_, 1, v___x_1225_);
        v___x_1227_ = l_Lean_Syntax_node2(v___x_1143_, v___x_1150_, v___x_1224_, v___x_1226_);
        v___x_1228_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__76;
        v___x_1229_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1229_, 0, v___x_1143_);
        crate::leanh::lean_ctor_set(v___x_1229_, 1, v___x_1228_);
        v___x_1230_ = l_Lean_Syntax_node3(
            v___x_1143_,
            v___x_1150_,
            v___x_1202_,
            v___x_1227_,
            v___x_1229_,
        );
        v___x_1231_ = l_Lean_Syntax_node6(
            v___x_1143_,
            v___x_1197_,
            v___x_1198_,
            v___x_1200_,
            v___x_1190_,
            v___x_1190_,
            v___x_1230_,
            v___x_1190_,
        );
        v___x_1232_ = l_Lean_Syntax_node3(
            v___x_1143_,
            v___x_1150_,
            v___x_1195_,
            v___x_1190_,
            v___x_1231_,
        );
        v___x_1233_ = l_Lean_Syntax_node1(v___x_1143_, v___x_1149_, v___x_1232_);
        v___x_1234_ = l_Lean_Syntax_node1(v___x_1143_, v___x_1148_, v___x_1233_);
        v___x_1235_ = l_Lean_Syntax_node3(
            v___x_1143_,
            v___x_1145_,
            v___x_1147_,
            v___x_1234_,
            v___x_1184_,
        );
        v___x_1236_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__77;
        v___x_1237_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1237_, 0, v___x_1143_);
        crate::leanh::lean_ctor_set(v___x_1237_, 1, v___x_1236_);
        v___x_1238_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78;
        v___x_1239_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79;
        v___x_1240_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1240_, 0, v___x_1143_);
        crate::leanh::lean_ctor_set(v___x_1240_, 1, v___x_1238_);
        v___x_1241_ = l_Lean_Syntax_node1(v___x_1143_, v___x_1239_, v___x_1240_);
        v___x_1242_ = l_Lean_Syntax_node3(
            v___x_1143_,
            v___x_1144_,
            v___x_1235_,
            v___x_1237_,
            v___x_1241_,
        );
        v___x_1243_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1243_, 0, v___x_1242_);
        crate::leanh::lean_ctor_set(v___x_1243_, 1, v_a_1134_);
        return v___x_1243_;
    }
}
pub unsafe fn l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2___boxed(
    mut v_x_1244_: *mut crate::leanh::LeanObject,
    mut v_a_1245_: *mut crate::leanh::LeanObject,
    mut v_a_1246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1247_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__2(v_x_1244_, v_a_1245_, v_a_1246_);
    crate::leanh::lean_dec_ref(v_a_1245_);
    return v_res_1247_;
}
pub unsafe fn _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1249_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__0;
    v___x_1250_ = l_String_toRawSubstring_x27(v___x_1249_);
    return v___x_1250_;
}
pub unsafe fn _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1266_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__7;
    v___x_1267_ = l_String_toRawSubstring_x27(v___x_1266_);
    return v___x_1267_;
}
pub unsafe fn l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3(
    mut v_x_1281_: *mut crate::leanh::LeanObject,
    mut v_a_1282_: *mut crate::leanh::LeanObject,
    mut v_a_1283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: u8 = 0;
    v___x_1284_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__1;
    v___x_1285_ = l_Lean_Syntax_isOfKind(v_x_1281_, v___x_1284_);
    if v___x_1285_ == 0 {
        let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1286_ = crate::leanh::lean_box(1);
        v___x_1287_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1287_, 0, v___x_1286_);
        crate::leanh::lean_ctor_set(v___x_1287_, 1, v_a_1283_);
        return v___x_1287_;
    } else {
        let mut v_quotContext_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1291_: u8 = 0;
        let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1288_ = crate::leanh::lean_ctor_get(v_a_1282_, 1);
        v_currMacroScope_1289_ = crate::leanh::lean_ctor_get(v_a_1282_, 2);
        v_ref_1290_ = crate::leanh::lean_ctor_get(v_a_1282_, 5);
        v___x_1291_ = 0;
        v___x_1292_ = l_Lean_SourceInfo_fromRef(v_ref_1290_, v___x_1291_);
        v___x_1293_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6;
        v___x_1294_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8;
        v___x_1295_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__9;
        crate::leanh::lean_inc_n(v___x_1292_, 50);
        v___x_1296_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1296_, 0, v___x_1292_);
        crate::leanh::lean_ctor_set(v___x_1296_, 1, v___x_1295_);
        v___x_1297_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11;
        v___x_1298_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13;
        v___x_1299_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__15;
        v___x_1300_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17;
        v___x_1301_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__18;
        v___x_1302_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1302_, 0, v___x_1292_);
        crate::leanh::lean_ctor_set(v___x_1302_, 1, v___x_1301_);
        v___x_1303_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19;
        v___x_1304_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20;
        v___x_1305_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1305_, 0, v___x_1292_);
        crate::leanh::lean_ctor_set(v___x_1305_, 1, v___x_1303_);
        v___x_1306_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__22;
        v___x_1307_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25;
        v___x_1308_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27;
        v___x_1309_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__29;
        v___x_1310_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31), core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31_once), _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31);
        v___x_1311_ = crate::leanh::lean_box(0);
        crate::leanh::lean_inc_n(v_currMacroScope_1289_, 3);
        crate::leanh::lean_inc_n(v_quotContext_1288_, 3);
        v___x_1312_ =
            l_Lean_addMacroScope(v_quotContext_1288_, v___x_1311_, v_currMacroScope_1289_);
        v___x_1313_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__35;
        v___x_1314_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1314_, 0, v___x_1292_);
        crate::leanh::lean_ctor_set(v___x_1314_, 1, v___x_1310_);
        crate::leanh::lean_ctor_set(v___x_1314_, 2, v___x_1312_);
        crate::leanh::lean_ctor_set(v___x_1314_, 3, v___x_1313_);
        v___x_1315_ = l_Lean_Syntax_node1(v___x_1292_, v___x_1309_, v___x_1314_);
        crate::leanh::lean_inc_ref(v___x_1296_);
        v___x_1316_ = l_Lean_Syntax_node2(v___x_1292_, v___x_1308_, v___x_1296_, v___x_1315_);
        v___x_1317_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37;
        v___x_1318_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__38;
        v___x_1319_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1319_, 0, v___x_1292_);
        crate::leanh::lean_ctor_set(v___x_1319_, 1, v___x_1318_);
        v___x_1320_ = l_Lean_Syntax_node1(v___x_1292_, v___x_1317_, v___x_1319_);
        v___x_1321_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__39;
        v___x_1322_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1322_, 0, v___x_1292_);
        crate::leanh::lean_ctor_set(v___x_1322_, 1, v___x_1321_);
        v___x_1323_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41;
        v___x_1324_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1), core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1_once), _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1);
        v___x_1325_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__2;
        v___x_1326_ =
            l_Lean_addMacroScope(v_quotContext_1288_, v___x_1325_, v_currMacroScope_1289_);
        v___x_1327_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__6;
        v___x_1328_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1328_, 0, v___x_1292_);
        crate::leanh::lean_ctor_set(v___x_1328_, 1, v___x_1324_);
        crate::leanh::lean_ctor_set(v___x_1328_, 2, v___x_1326_);
        crate::leanh::lean_ctor_set(v___x_1328_, 3, v___x_1327_);
        crate::leanh::lean_inc_n(v___x_1320_, 2);
        v___x_1329_ = l_Lean_Syntax_node1(v___x_1292_, v___x_1299_, v___x_1320_);
        v___x_1330_ = l_Lean_Syntax_node2(v___x_1292_, v___x_1323_, v___x_1328_, v___x_1329_);
        v___x_1331_ = l_Lean_Syntax_node1(v___x_1292_, v___x_1299_, v___x_1330_);
        v___x_1332_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__52;
        v___x_1333_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1333_, 0, v___x_1292_);
        crate::leanh::lean_ctor_set(v___x_1333_, 1, v___x_1332_);
        crate::leanh::lean_inc_ref_n(v___x_1333_, 2);
        crate::leanh::lean_inc(v___x_1316_);
        v___x_1334_ = l_Lean_Syntax_node5(
            v___x_1292_,
            v___x_1307_,
            v___x_1316_,
            v___x_1320_,
            v___x_1322_,
            v___x_1331_,
            v___x_1333_,
        );
        v___x_1335_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__53;
        v___x_1336_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1336_, 0, v___x_1292_);
        crate::leanh::lean_ctor_set(v___x_1336_, 1, v___x_1335_);
        v___x_1337_ = l_Lean_Syntax_node3(
            v___x_1292_,
            v___x_1306_,
            v___x_1334_,
            v___x_1336_,
            v___x_1320_,
        );
        v___x_1338_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54), core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54_once), _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54);
        v___x_1339_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1339_, 0, v___x_1292_);
        crate::leanh::lean_ctor_set(v___x_1339_, 1, v___x_1299_);
        crate::leanh::lean_ctor_set(v___x_1339_, 2, v___x_1338_);
        crate::leanh::lean_inc_ref_n(v___x_1339_, 7);
        v___x_1340_ = l_Lean_Syntax_node3(
            v___x_1292_,
            v___x_1304_,
            v___x_1305_,
            v___x_1337_,
            v___x_1339_,
        );
        v___x_1341_ = l_Lean_Syntax_node1(v___x_1292_, v___x_1299_, v___x_1340_);
        v___x_1342_ = l_Lean_Syntax_node1(v___x_1292_, v___x_1298_, v___x_1341_);
        v___x_1343_ = l_Lean_Syntax_node1(v___x_1292_, v___x_1297_, v___x_1342_);
        v___x_1344_ = l_Lean_Syntax_node2(v___x_1292_, v___x_1300_, v___x_1302_, v___x_1343_);
        v___x_1345_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55;
        v___x_1346_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56;
        v___x_1347_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1347_, 0, v___x_1292_);
        crate::leanh::lean_ctor_set(v___x_1347_, 1, v___x_1345_);
        v___x_1348_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58;
        v___x_1349_ = l_Lean_Syntax_node1(v___x_1292_, v___x_1348_, v___x_1339_);
        v___x_1350_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__59;
        v___x_1351_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1351_, 0, v___x_1292_);
        crate::leanh::lean_ctor_set(v___x_1351_, 1, v___x_1350_);
        v___x_1352_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61;
        v___x_1353_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__8), core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__8_once), _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__8);
        v___x_1354_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__9;
        v___x_1355_ =
            l_Lean_addMacroScope(v_quotContext_1288_, v___x_1354_, v_currMacroScope_1289_);
        v___x_1356_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__12;
        v___x_1357_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1357_, 0, v___x_1292_);
        crate::leanh::lean_ctor_set(v___x_1357_, 1, v___x_1353_);
        crate::leanh::lean_ctor_set(v___x_1357_, 2, v___x_1355_);
        crate::leanh::lean_ctor_set(v___x_1357_, 3, v___x_1356_);
        v___x_1358_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69;
        v___x_1359_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71;
        v___x_1360_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__72;
        v___x_1361_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1361_, 0, v___x_1292_);
        crate::leanh::lean_ctor_set(v___x_1361_, 1, v___x_1360_);
        v___x_1362_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73;
        v___x_1363_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74;
        v___x_1364_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1364_, 0, v___x_1292_);
        crate::leanh::lean_ctor_set(v___x_1364_, 1, v___x_1362_);
        v___x_1365_ = l_Lean_Syntax_node1(v___x_1292_, v___x_1363_, v___x_1364_);
        v___x_1366_ = l_Lean_Syntax_node1(v___x_1292_, v___x_1299_, v___x_1365_);
        v___x_1367_ = l_Lean_Syntax_node1(v___x_1292_, v___x_1298_, v___x_1366_);
        v___x_1368_ = l_Lean_Syntax_node1(v___x_1292_, v___x_1297_, v___x_1367_);
        v___x_1369_ = l_Lean_Syntax_node2(v___x_1292_, v___x_1359_, v___x_1361_, v___x_1368_);
        v___x_1370_ = l_Lean_Syntax_node3(
            v___x_1292_,
            v___x_1358_,
            v___x_1316_,
            v___x_1369_,
            v___x_1333_,
        );
        v___x_1371_ = l_Lean_Syntax_node1(v___x_1292_, v___x_1299_, v___x_1370_);
        v___x_1372_ = l_Lean_Syntax_node2(v___x_1292_, v___x_1323_, v___x_1357_, v___x_1371_);
        v___x_1373_ = l_Lean_Syntax_node3(
            v___x_1292_,
            v___x_1352_,
            v___x_1339_,
            v___x_1339_,
            v___x_1372_,
        );
        v___x_1374_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__75;
        v___x_1375_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1375_, 0, v___x_1292_);
        crate::leanh::lean_ctor_set(v___x_1375_, 1, v___x_1374_);
        v___x_1376_ = l_Lean_Syntax_node2(v___x_1292_, v___x_1299_, v___x_1373_, v___x_1375_);
        v___x_1377_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__76;
        v___x_1378_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1378_, 0, v___x_1292_);
        crate::leanh::lean_ctor_set(v___x_1378_, 1, v___x_1377_);
        v___x_1379_ = l_Lean_Syntax_node3(
            v___x_1292_,
            v___x_1299_,
            v___x_1351_,
            v___x_1376_,
            v___x_1378_,
        );
        v___x_1380_ = l_Lean_Syntax_node6(
            v___x_1292_,
            v___x_1346_,
            v___x_1347_,
            v___x_1349_,
            v___x_1339_,
            v___x_1339_,
            v___x_1379_,
            v___x_1339_,
        );
        v___x_1381_ = l_Lean_Syntax_node3(
            v___x_1292_,
            v___x_1299_,
            v___x_1344_,
            v___x_1339_,
            v___x_1380_,
        );
        v___x_1382_ = l_Lean_Syntax_node1(v___x_1292_, v___x_1298_, v___x_1381_);
        v___x_1383_ = l_Lean_Syntax_node1(v___x_1292_, v___x_1297_, v___x_1382_);
        v___x_1384_ = l_Lean_Syntax_node3(
            v___x_1292_,
            v___x_1294_,
            v___x_1296_,
            v___x_1383_,
            v___x_1333_,
        );
        v___x_1385_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__77;
        v___x_1386_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1386_, 0, v___x_1292_);
        crate::leanh::lean_ctor_set(v___x_1386_, 1, v___x_1385_);
        v___x_1387_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78;
        v___x_1388_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79;
        v___x_1389_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1389_, 0, v___x_1292_);
        crate::leanh::lean_ctor_set(v___x_1389_, 1, v___x_1387_);
        v___x_1390_ = l_Lean_Syntax_node1(v___x_1292_, v___x_1388_, v___x_1389_);
        v___x_1391_ = l_Lean_Syntax_node3(
            v___x_1292_,
            v___x_1293_,
            v___x_1384_,
            v___x_1386_,
            v___x_1390_,
        );
        v___x_1392_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1392_, 0, v___x_1391_);
        crate::leanh::lean_ctor_set(v___x_1392_, 1, v_a_1283_);
        return v___x_1392_;
    }
}
pub unsafe fn l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___boxed(
    mut v_x_1393_: *mut crate::leanh::LeanObject,
    mut v_a_1394_: *mut crate::leanh::LeanObject,
    mut v_a_1395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1396_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3(v_x_1393_, v_a_1394_, v_a_1395_);
    crate::leanh::lean_dec_ref(v_a_1394_);
    return v_res_1396_;
}
pub unsafe fn _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1398_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__0;
    v___x_1399_ = l_String_toRawSubstring_x27(v___x_1398_);
    return v___x_1399_;
}
pub unsafe fn l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4(
    mut v_x_1413_: *mut crate::leanh::LeanObject,
    mut v_a_1414_: *mut crate::leanh::LeanObject,
    mut v_a_1415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: u8 = 0;
    v___x_1416_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__1;
    v___x_1417_ = l_Lean_Syntax_isOfKind(v_x_1413_, v___x_1416_);
    if v___x_1417_ == 0 {
        let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1418_ = crate::leanh::lean_box(1);
        v___x_1419_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1419_, 0, v___x_1418_);
        crate::leanh::lean_ctor_set(v___x_1419_, 1, v_a_1415_);
        return v___x_1419_;
    } else {
        let mut v_quotContext_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1423_: u8 = 0;
        let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_1420_ = crate::leanh::lean_ctor_get(v_a_1414_, 1);
        v_currMacroScope_1421_ = crate::leanh::lean_ctor_get(v_a_1414_, 2);
        v_ref_1422_ = crate::leanh::lean_ctor_get(v_a_1414_, 5);
        v___x_1423_ = 0;
        v___x_1424_ = l_Lean_SourceInfo_fromRef(v_ref_1422_, v___x_1423_);
        v___x_1425_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__6;
        v___x_1426_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__8;
        v___x_1427_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__9;
        crate::leanh::lean_inc_n(v___x_1424_, 50);
        v___x_1428_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1428_, 0, v___x_1424_);
        crate::leanh::lean_ctor_set(v___x_1428_, 1, v___x_1427_);
        v___x_1429_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__11;
        v___x_1430_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__13;
        v___x_1431_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__15;
        v___x_1432_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__17;
        v___x_1433_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__18;
        v___x_1434_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1434_, 0, v___x_1424_);
        crate::leanh::lean_ctor_set(v___x_1434_, 1, v___x_1433_);
        v___x_1435_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__19;
        v___x_1436_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__20;
        v___x_1437_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1437_, 0, v___x_1424_);
        crate::leanh::lean_ctor_set(v___x_1437_, 1, v___x_1435_);
        v___x_1438_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__22;
        v___x_1439_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__25;
        v___x_1440_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__27;
        v___x_1441_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__29;
        v___x_1442_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31), core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31_once), _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__31);
        v___x_1443_ = crate::leanh::lean_box(0);
        crate::leanh::lean_inc_n(v_currMacroScope_1421_, 3);
        crate::leanh::lean_inc_n(v_quotContext_1420_, 3);
        v___x_1444_ =
            l_Lean_addMacroScope(v_quotContext_1420_, v___x_1443_, v_currMacroScope_1421_);
        v___x_1445_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__35;
        v___x_1446_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1446_, 0, v___x_1424_);
        crate::leanh::lean_ctor_set(v___x_1446_, 1, v___x_1442_);
        crate::leanh::lean_ctor_set(v___x_1446_, 2, v___x_1444_);
        crate::leanh::lean_ctor_set(v___x_1446_, 3, v___x_1445_);
        v___x_1447_ = l_Lean_Syntax_node1(v___x_1424_, v___x_1441_, v___x_1446_);
        crate::leanh::lean_inc_ref(v___x_1428_);
        v___x_1448_ = l_Lean_Syntax_node2(v___x_1424_, v___x_1440_, v___x_1428_, v___x_1447_);
        v___x_1449_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__37;
        v___x_1450_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__38;
        v___x_1451_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1451_, 0, v___x_1424_);
        crate::leanh::lean_ctor_set(v___x_1451_, 1, v___x_1450_);
        v___x_1452_ = l_Lean_Syntax_node1(v___x_1424_, v___x_1449_, v___x_1451_);
        v___x_1453_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__39;
        v___x_1454_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1454_, 0, v___x_1424_);
        crate::leanh::lean_ctor_set(v___x_1454_, 1, v___x_1453_);
        v___x_1455_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__41;
        v___x_1456_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1), core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1_once), _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__1);
        v___x_1457_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__2;
        v___x_1458_ =
            l_Lean_addMacroScope(v_quotContext_1420_, v___x_1457_, v_currMacroScope_1421_);
        v___x_1459_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__3___closed__6;
        v___x_1460_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1460_, 0, v___x_1424_);
        crate::leanh::lean_ctor_set(v___x_1460_, 1, v___x_1456_);
        crate::leanh::lean_ctor_set(v___x_1460_, 2, v___x_1458_);
        crate::leanh::lean_ctor_set(v___x_1460_, 3, v___x_1459_);
        crate::leanh::lean_inc_n(v___x_1452_, 2);
        v___x_1461_ = l_Lean_Syntax_node1(v___x_1424_, v___x_1431_, v___x_1452_);
        v___x_1462_ = l_Lean_Syntax_node2(v___x_1424_, v___x_1455_, v___x_1460_, v___x_1461_);
        v___x_1463_ = l_Lean_Syntax_node1(v___x_1424_, v___x_1431_, v___x_1462_);
        v___x_1464_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__52;
        v___x_1465_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1465_, 0, v___x_1424_);
        crate::leanh::lean_ctor_set(v___x_1465_, 1, v___x_1464_);
        crate::leanh::lean_inc_ref_n(v___x_1465_, 2);
        crate::leanh::lean_inc(v___x_1448_);
        v___x_1466_ = l_Lean_Syntax_node5(
            v___x_1424_,
            v___x_1439_,
            v___x_1448_,
            v___x_1452_,
            v___x_1454_,
            v___x_1463_,
            v___x_1465_,
        );
        v___x_1467_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__53;
        v___x_1468_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1468_, 0, v___x_1424_);
        crate::leanh::lean_ctor_set(v___x_1468_, 1, v___x_1467_);
        v___x_1469_ = l_Lean_Syntax_node3(
            v___x_1424_,
            v___x_1438_,
            v___x_1466_,
            v___x_1468_,
            v___x_1452_,
        );
        v___x_1470_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54), core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54_once), _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__54);
        v___x_1471_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1471_, 0, v___x_1424_);
        crate::leanh::lean_ctor_set(v___x_1471_, 1, v___x_1431_);
        crate::leanh::lean_ctor_set(v___x_1471_, 2, v___x_1470_);
        crate::leanh::lean_inc_ref_n(v___x_1471_, 7);
        v___x_1472_ = l_Lean_Syntax_node3(
            v___x_1424_,
            v___x_1436_,
            v___x_1437_,
            v___x_1469_,
            v___x_1471_,
        );
        v___x_1473_ = l_Lean_Syntax_node1(v___x_1424_, v___x_1431_, v___x_1472_);
        v___x_1474_ = l_Lean_Syntax_node1(v___x_1424_, v___x_1430_, v___x_1473_);
        v___x_1475_ = l_Lean_Syntax_node1(v___x_1424_, v___x_1429_, v___x_1474_);
        v___x_1476_ = l_Lean_Syntax_node2(v___x_1424_, v___x_1432_, v___x_1434_, v___x_1475_);
        v___x_1477_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__55;
        v___x_1478_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__56;
        v___x_1479_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1479_, 0, v___x_1424_);
        crate::leanh::lean_ctor_set(v___x_1479_, 1, v___x_1477_);
        v___x_1480_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__58;
        v___x_1481_ = l_Lean_Syntax_node1(v___x_1424_, v___x_1480_, v___x_1471_);
        v___x_1482_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__59;
        v___x_1483_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1483_, 0, v___x_1424_);
        crate::leanh::lean_ctor_set(v___x_1483_, 1, v___x_1482_);
        v___x_1484_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__61;
        v___x_1485_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__1), core::ptr::addr_of_mut!(l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__1_once), _init_l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__1);
        v___x_1486_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__2;
        v___x_1487_ =
            l_Lean_addMacroScope(v_quotContext_1420_, v___x_1486_, v_currMacroScope_1421_);
        v___x_1488_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___closed__5;
        v___x_1489_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1489_, 0, v___x_1424_);
        crate::leanh::lean_ctor_set(v___x_1489_, 1, v___x_1485_);
        crate::leanh::lean_ctor_set(v___x_1489_, 2, v___x_1487_);
        crate::leanh::lean_ctor_set(v___x_1489_, 3, v___x_1488_);
        v___x_1490_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__69;
        v___x_1491_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__71;
        v___x_1492_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__72;
        v___x_1493_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1493_, 0, v___x_1424_);
        crate::leanh::lean_ctor_set(v___x_1493_, 1, v___x_1492_);
        v___x_1494_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__73;
        v___x_1495_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__74;
        v___x_1496_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1496_, 0, v___x_1424_);
        crate::leanh::lean_ctor_set(v___x_1496_, 1, v___x_1494_);
        v___x_1497_ = l_Lean_Syntax_node1(v___x_1424_, v___x_1495_, v___x_1496_);
        v___x_1498_ = l_Lean_Syntax_node1(v___x_1424_, v___x_1431_, v___x_1497_);
        v___x_1499_ = l_Lean_Syntax_node1(v___x_1424_, v___x_1430_, v___x_1498_);
        v___x_1500_ = l_Lean_Syntax_node1(v___x_1424_, v___x_1429_, v___x_1499_);
        v___x_1501_ = l_Lean_Syntax_node2(v___x_1424_, v___x_1491_, v___x_1493_, v___x_1500_);
        v___x_1502_ = l_Lean_Syntax_node3(
            v___x_1424_,
            v___x_1490_,
            v___x_1448_,
            v___x_1501_,
            v___x_1465_,
        );
        v___x_1503_ = l_Lean_Syntax_node1(v___x_1424_, v___x_1431_, v___x_1502_);
        v___x_1504_ = l_Lean_Syntax_node2(v___x_1424_, v___x_1455_, v___x_1489_, v___x_1503_);
        v___x_1505_ = l_Lean_Syntax_node3(
            v___x_1424_,
            v___x_1484_,
            v___x_1471_,
            v___x_1471_,
            v___x_1504_,
        );
        v___x_1506_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__75;
        v___x_1507_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1507_, 0, v___x_1424_);
        crate::leanh::lean_ctor_set(v___x_1507_, 1, v___x_1506_);
        v___x_1508_ = l_Lean_Syntax_node2(v___x_1424_, v___x_1431_, v___x_1505_, v___x_1507_);
        v___x_1509_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__76;
        v___x_1510_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1510_, 0, v___x_1424_);
        crate::leanh::lean_ctor_set(v___x_1510_, 1, v___x_1509_);
        v___x_1511_ = l_Lean_Syntax_node3(
            v___x_1424_,
            v___x_1431_,
            v___x_1483_,
            v___x_1508_,
            v___x_1510_,
        );
        v___x_1512_ = l_Lean_Syntax_node6(
            v___x_1424_,
            v___x_1478_,
            v___x_1479_,
            v___x_1481_,
            v___x_1471_,
            v___x_1471_,
            v___x_1511_,
            v___x_1471_,
        );
        v___x_1513_ = l_Lean_Syntax_node3(
            v___x_1424_,
            v___x_1431_,
            v___x_1476_,
            v___x_1471_,
            v___x_1512_,
        );
        v___x_1514_ = l_Lean_Syntax_node1(v___x_1424_, v___x_1430_, v___x_1513_);
        v___x_1515_ = l_Lean_Syntax_node1(v___x_1424_, v___x_1429_, v___x_1514_);
        v___x_1516_ = l_Lean_Syntax_node3(
            v___x_1424_,
            v___x_1426_,
            v___x_1428_,
            v___x_1515_,
            v___x_1465_,
        );
        v___x_1517_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__77;
        v___x_1518_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1518_, 0, v___x_1424_);
        crate::leanh::lean_ctor_set(v___x_1518_, 1, v___x_1517_);
        v___x_1519_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__78;
        v___x_1520_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__1___closed__79;
        v___x_1521_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1521_, 0, v___x_1424_);
        crate::leanh::lean_ctor_set(v___x_1521_, 1, v___x_1519_);
        v___x_1522_ = l_Lean_Syntax_node1(v___x_1424_, v___x_1520_, v___x_1521_);
        v___x_1523_ = l_Lean_Syntax_node3(
            v___x_1424_,
            v___x_1425_,
            v___x_1516_,
            v___x_1518_,
            v___x_1522_,
        );
        v___x_1524_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1524_, 0, v___x_1523_);
        crate::leanh::lean_ctor_set(v___x_1524_, 1, v_a_1415_);
        return v___x_1524_;
    }
}
pub unsafe fn l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4___boxed(
    mut v_x_1525_: *mut crate::leanh::LeanObject,
    mut v_a_1526_: *mut crate::leanh::LeanObject,
    mut v_a_1527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1528_ = l_String___aux__Init__Data__String__Termination______macroRules__tacticDecreasing__trivial__4(v_x_1525_, v_a_1526_, v_a_1527_);
    crate::leanh::lean_dec_ref(v_a_1526_);
    return v_res_1528_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Termination(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Lemmas_Splits(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Termination(
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
pub unsafe fn initialize_Init_Data_String_Termination(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Lemmas_Splits(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Termination(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Termination(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Termination(builtin);
}
