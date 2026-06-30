// Lean compiler output
// Module: Init.Data.Slice.Notation
// Imports: Init.Data.Range.Polymorphic.PRange
use crate::r#gen::Init::Data::Range::Polymorphic::PRange::{
    initialize_Init_Data_Range_Polymorphic_PRange,
    runtime_initialize_Init_Data_Range_Polymorphic_PRange,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 95, 95, 91, 95, 93, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__0_value) as *mut leanh::LeanObject,17746073143502587047 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__3_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 42, 46, 46, 46, 42, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__3_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__3_value) as *mut leanh::LeanObject,15812821569646102790 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__5_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 95, 46, 46, 46, 42, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__5_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__5_value) as *mut leanh::LeanObject,12901981646182791257 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__7_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 101, 114, 109, 95, 60, 46, 46, 46, 42, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__7_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__7_value) as *mut leanh::LeanObject,18313290646982499243 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__9_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 101, 114, 109, 42, 46, 46, 46, 60, 95, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__9_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__9_value) as *mut leanh::LeanObject,17665753292882927436 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__11_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 101, 114, 109, 95, 46, 46, 46, 60, 95, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__11_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__12_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__12_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__11_value) as *mut leanh::LeanObject,4456104206502475912 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__13_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [116, 101, 114, 109, 95, 60, 46, 46, 46, 60, 95, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__13_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__14_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__14_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__13_value) as *mut leanh::LeanObject,17893611459657078921 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__15_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 42, 46, 46, 46, 95, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__15_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__16_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__16_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__16_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__15_value) as *mut leanh::LeanObject,10703712094186559148 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__16_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__17_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 95, 46, 46, 46, 95, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__17_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__18_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__18_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__18_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__17_value) as *mut leanh::LeanObject,5394156637022377744 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__18_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__19_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 101, 114, 109, 95, 60, 46, 46, 46, 95, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__19_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__20_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__20_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__20_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__19_value) as *mut leanh::LeanObject,3473794126537410698 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__20_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__21_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 101, 114, 109, 42, 46, 46, 46, 61, 95, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__21_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__22_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__22_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__22_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__21_value) as *mut leanh::LeanObject,897828399751270016 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__22_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__23_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 101, 114, 109, 95, 46, 46, 46, 61, 95, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__23_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__24_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__24_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__24_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__23_value) as *mut leanh::LeanObject,8312988086032421140 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__24_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__25_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [116, 101, 114, 109, 95, 60, 46, 46, 46, 61, 95, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__25_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__26_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__26_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__26_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__25_value) as *mut leanh::LeanObject,15212140180363167796 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__26_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__27_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__27_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__28_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__28_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__29_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__29_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__30_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__30_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__31_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__27_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__31_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__31_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__28_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__31_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__31_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__29_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__31_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__31_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__30_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__31_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__32_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [82, 111, 99, 46, 83, 108, 105, 99, 101, 97, 98, 108, 101, 46, 109, 107, 83, 108, 105, 99, 101, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__32_value) as *mut leanh::LeanObject;
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__33_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__33: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__34_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 111, 99, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__34: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__34_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__35_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [83, 108, 105, 99, 101, 97, 98, 108, 101, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__35: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__35_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__36_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [109, 107, 83, 108, 105, 99, 101, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__36: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__36_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__37_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__34_value) as *mut leanh::LeanObject,9514074055516749235 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__37_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__37_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__35_value) as *mut leanh::LeanObject,4256875253782895259 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__37_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__37_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__36_value) as *mut leanh::LeanObject,13890204570387730500 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__37: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__37_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__38_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__38_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__38_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__34_value) as *mut leanh::LeanObject,16615662997495850524 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__38_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__38_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__35_value) as *mut leanh::LeanObject,436832230513359808 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__38_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__38_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__36_value) as *mut leanh::LeanObject,16356126388992858779 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__38: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__38_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__39_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__38_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__39: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__39_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__40_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__39_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__40: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__40_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__41_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__41: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__41_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__42_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__41_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__42: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__42_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__43_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [60, 46, 46, 46, 61, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__43: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__43_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__44_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [82, 99, 99, 46, 83, 108, 105, 99, 101, 97, 98, 108, 101, 46, 109, 107, 83, 108, 105, 99, 101, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__44: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__44_value) as *mut leanh::LeanObject;
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__45_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__45: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__46_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 99, 99, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__46: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__46_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__47_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__46_value) as *mut leanh::LeanObject,16265292064117835183 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__47_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__47_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__35_value) as *mut leanh::LeanObject,3173869360043792623 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__47_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__47_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__36_value) as *mut leanh::LeanObject,1700231103566666048 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__47: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__47_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__48_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__48_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__48_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__46_value) as *mut leanh::LeanObject,16437420457889295896 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__48_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__48_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__35_value) as *mut leanh::LeanObject,11695111600615160340 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__48_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__48_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__36_value) as *mut leanh::LeanObject,18381529557286608343 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__48: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__48_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__49_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__48_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__49: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__49_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__50_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__49_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__50: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__50_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__51_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [46, 46, 46, 61, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__51: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__51_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__52_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [82, 105, 99, 46, 83, 108, 105, 99, 101, 97, 98, 108, 101, 46, 109, 107, 83, 108, 105, 99, 101, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__52: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__52_value) as *mut leanh::LeanObject;
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__53_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__53: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__54_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 105, 99, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__54: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__54_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__55_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__54_value) as *mut leanh::LeanObject,16004387948037561718 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__55_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__55_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__35_value) as *mut leanh::LeanObject,11042411126426849266 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__55_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__55_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__36_value) as *mut leanh::LeanObject,3138196065819806241 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__55: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__55_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__56_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__56_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__56_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__54_value) as *mut leanh::LeanObject,8649810267064386489 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__56_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__56_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__35_value) as *mut leanh::LeanObject,15376446239911630025 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__56_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__56_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__36_value) as *mut leanh::LeanObject,622936976997620062 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__56: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__56_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__57_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__56_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__57: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__57_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__58_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__57_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__58: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__58_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__59_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [42, 46, 46, 46, 61, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__59: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__59_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__60_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [82, 111, 111, 46, 83, 108, 105, 99, 101, 97, 98, 108, 101, 46, 109, 107, 83, 108, 105, 99, 101, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__60: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__60_value) as *mut leanh::LeanObject;
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__61_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__61: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__62_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 111, 111, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__62: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__62_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__63_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__62_value) as *mut leanh::LeanObject,1583659881074599201 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__63_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__63_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__35_value) as *mut leanh::LeanObject,18070073562520003393 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__63_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__63_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__36_value) as *mut leanh::LeanObject,8215950685138760582 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__63: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__63_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__64_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__64_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__64_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__62_value) as *mut leanh::LeanObject,17971250720669795982 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__64_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__64_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__35_value) as *mut leanh::LeanObject,1795980445182000570 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__64_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__64_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__36_value) as *mut leanh::LeanObject,13867136215007460921 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__64: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__64_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__65_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__64_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__65: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__65_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__66_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__65_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__66: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__66_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__67_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [60, 46, 46, 46, 60, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__67: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__67_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__68_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [82, 99, 111, 46, 83, 108, 105, 99, 101, 97, 98, 108, 101, 46, 109, 107, 83, 108, 105, 99, 101, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__68: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__68_value) as *mut leanh::LeanObject;
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__69_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__69: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__70_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 99, 111, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__70: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__70_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__71_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__70_value) as *mut leanh::LeanObject,16672968270688273557 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__71_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__71_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__35_value) as *mut leanh::LeanObject,6997656838696710525 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__71_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__71_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__36_value) as *mut leanh::LeanObject,1551068597178314042 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__71: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__71_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__72_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__72_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__72_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__70_value) as *mut leanh::LeanObject,36003929318889298 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__72_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__72_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__35_value) as *mut leanh::LeanObject,7466204601942245798 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__72_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__72_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__36_value) as *mut leanh::LeanObject,1012977872292886333 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__72: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__72_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__73_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__72_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__73: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__73_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__74_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__73_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__74: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__74_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__75_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [46, 46, 46, 60, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__75: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__75_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__76_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [82, 105, 111, 46, 83, 108, 105, 99, 101, 97, 98, 108, 101, 46, 109, 107, 83, 108, 105, 99, 101, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__76: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__76_value) as *mut leanh::LeanObject;
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__77_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__77: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__78_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 105, 111, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__78: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__78_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__79_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__78_value) as *mut leanh::LeanObject,17569179190824060398 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__79_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__79_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__35_value) as *mut leanh::LeanObject,16272545448027114010 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__79_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__79_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__36_value) as *mut leanh::LeanObject,6746820766576989273 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__79: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__79_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__80_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__80_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__80_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__78_value) as *mut leanh::LeanObject,10504416010916204673 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__80_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__80_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__35_value) as *mut leanh::LeanObject,14285992690111286561 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__80_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__80_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__36_value) as *mut leanh::LeanObject,13777918632049776038 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__80: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__80_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__81_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__80_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__81: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__81_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__82_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__81_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__82: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__82_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__83_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [42, 46, 46, 46, 60, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__83: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__83_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__84_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [82, 111, 105, 46, 83, 108, 105, 99, 101, 97, 98, 108, 101, 46, 109, 107, 83, 108, 105, 99, 101, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__84: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__84_value) as *mut leanh::LeanObject;
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__85_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__85: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__86_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 111, 105, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__86: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__86_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__87_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__86_value) as *mut leanh::LeanObject,17849391023096305096 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__87_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__87_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__35_value) as *mut leanh::LeanObject,779226333974747812 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__87_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__87_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__36_value) as *mut leanh::LeanObject,13203777998749427559 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__87: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__87_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__88_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__88_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__88_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__86_value) as *mut leanh::LeanObject,16217565746838389087 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__88_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__88_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__35_value) as *mut leanh::LeanObject,4576606366299676223 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__88_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__88_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__36_value) as *mut leanh::LeanObject,12678803211981516240 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__88: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__88_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__89_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__88_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__89: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__89_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__90_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__89_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__90: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__90_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__91_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [60, 46, 46, 46, 42, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__91: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__91_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__92_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [82, 99, 105, 46, 83, 108, 105, 99, 101, 97, 98, 108, 101, 46, 109, 107, 83, 108, 105, 99, 101, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__92: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__92_value) as *mut leanh::LeanObject;
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__93_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__93: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__94_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 99, 105, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__94: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__94_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__95_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__94_value) as *mut leanh::LeanObject,6989692408478346940 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__95_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__95_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__35_value) as *mut leanh::LeanObject,14378547782831537120 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__95_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__95_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__36_value) as *mut leanh::LeanObject,6598577096796432379 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__95: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__95_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__96_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__96_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__96_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__94_value) as *mut leanh::LeanObject,1178185768520342099 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__96_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__96_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__35_value) as *mut leanh::LeanObject,8790649933911988795 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__96_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__96_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__36_value) as *mut leanh::LeanObject,9821613100516091940 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__96: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__96_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__97_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__96_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__97: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__97_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__98_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__97_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__98: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__98_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__99_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [46, 46, 46, 42, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__99: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__99_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__100_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [82, 105, 105, 46, 83, 108, 105, 99, 101, 97, 98, 108, 101, 46, 109, 107, 83, 108, 105, 99, 101, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__100: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__100_value) as *mut leanh::LeanObject;
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__101_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__101: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__102_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 105, 105, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__102: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__102_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__103_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__102_value) as *mut leanh::LeanObject,8021574905279043171 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__103_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__103_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__35_value) as *mut leanh::LeanObject,13918620089094529579 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__103_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__103_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__36_value) as *mut leanh::LeanObject,9312964066289329876 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__103: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__103_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__104_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__104_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__104_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__102_value) as *mut leanh::LeanObject,15880302354919066316 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__104_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__104_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__35_value) as *mut leanh::LeanObject,534860834173438288 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__104_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__104_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__36_value) as *mut leanh::LeanObject,15428048834389853291 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__104: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__104_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__105_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__104_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__105: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__105_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__106_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__105_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__106: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__106_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__107_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [42, 46, 46, 46, 42, 0]};
static mut l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__107: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__107_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__33()
-> *mut leanh::LeanObject {
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_573_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__32;
    v___x_574_ = l_String_toRawSubstring_x27(v___x_573_);
    return v___x_574_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__45()
-> *mut leanh::LeanObject {
    let mut v___x_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_598_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__44;
    v___x_599_ = l_String_toRawSubstring_x27(v___x_598_);
    return v___x_599_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__53()
-> *mut leanh::LeanObject {
    let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_618_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__52;
    v___x_619_ = l_String_toRawSubstring_x27(v___x_618_);
    return v___x_619_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__61()
-> *mut leanh::LeanObject {
    let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_638_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__60;
    v___x_639_ = l_String_toRawSubstring_x27(v___x_638_);
    return v___x_639_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__69()
-> *mut leanh::LeanObject {
    let mut v___x_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_658_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__68;
    v___x_659_ = l_String_toRawSubstring_x27(v___x_658_);
    return v___x_659_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__77()
-> *mut leanh::LeanObject {
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_678_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__76;
    v___x_679_ = l_String_toRawSubstring_x27(v___x_678_);
    return v___x_679_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__85()
-> *mut leanh::LeanObject {
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_698_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__84;
    v___x_699_ = l_String_toRawSubstring_x27(v___x_698_);
    return v___x_699_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__93()
-> *mut leanh::LeanObject {
    let mut v___x_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_718_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__92;
    v___x_719_ = l_String_toRawSubstring_x27(v___x_718_);
    return v___x_719_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__101()
-> *mut leanh::LeanObject {
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_738_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__100;
    v___x_739_ = l_String_toRawSubstring_x27(v___x_738_);
    return v___x_739_;
}
pub unsafe fn l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1(
    mut v_x_757_: *mut leanh::LeanObject,
    mut v_a_758_: *mut leanh::LeanObject,
    mut v_a_759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: u8 = 0;
    v___x_760_ =
        l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__1;
    leanh::lean_inc(v_x_757_);
    v___x_761_ = l_Lean_Syntax_isOfKind(v_x_757_, v___x_760_);
    if v___x_761_ == 0 {
        let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_757_);
        v___x_762_ = leanh::lean_box(1);
        v___x_763_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_763_, 0, v___x_762_);
        leanh::lean_ctor_set(v___x_763_, 1, v_a_759_);
        return v___x_763_;
    } else {
        let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_769_: u8 = 0;
        v___x_764_ = leanh::lean_unsigned_to_nat(0);
        v___x_765_ = l_Lean_Syntax_getArg(v_x_757_, v___x_764_);
        v___x_766_ = leanh::lean_unsigned_to_nat(2);
        v___x_767_ = l_Lean_Syntax_getArg(v_x_757_, v___x_766_);
        leanh::lean_dec(v_x_757_);
        v___x_768_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__4;
        leanh::lean_inc(v___x_767_);
        v___x_769_ = l_Lean_Syntax_isOfKind(v___x_767_, v___x_768_);
        if v___x_769_ == 0 {
            let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_771_: u8 = 0;
            v___x_770_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__6;
            leanh::lean_inc(v___x_767_);
            v___x_771_ = l_Lean_Syntax_isOfKind(v___x_767_, v___x_770_);
            if v___x_771_ == 0 {
                let mut v___x_772_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_773_: u8 = 0;
                v___x_772_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__8;
                leanh::lean_inc(v___x_767_);
                v___x_773_ = l_Lean_Syntax_isOfKind(v___x_767_, v___x_772_);
                if v___x_773_ == 0 {
                    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_776_: u8 = 0;
                    v___x_774_ = leanh::lean_unsigned_to_nat(1);
                    v___x_775_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__10;
                    leanh::lean_inc(v___x_767_);
                    v___x_776_ = l_Lean_Syntax_isOfKind(v___x_767_, v___x_775_);
                    if v___x_776_ == 0 {
                        let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_778_: u8 = 0;
                        v___x_777_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__12;
                        leanh::lean_inc(v___x_767_);
                        v___x_778_ = l_Lean_Syntax_isOfKind(v___x_767_, v___x_777_);
                        if v___x_778_ == 0 {
                            let mut v___x_779_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_780_: u8 = 0;
                            v___x_779_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__14;
                            leanh::lean_inc(v___x_767_);
                            v___x_780_ = l_Lean_Syntax_isOfKind(v___x_767_, v___x_779_);
                            if v___x_780_ == 0 {
                                let mut v___x_781_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_782_: u8 = 0;
                                v___x_781_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__16;
                                leanh::lean_inc(v___x_767_);
                                v___x_782_ = l_Lean_Syntax_isOfKind(v___x_767_, v___x_781_);
                                if v___x_782_ == 0 {
                                    let mut v___x_783_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_784_: u8 = 0;
                                    v___x_783_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__18;
                                    leanh::lean_inc(v___x_767_);
                                    v___x_784_ = l_Lean_Syntax_isOfKind(v___x_767_, v___x_783_);
                                    if v___x_784_ == 0 {
                                        let mut v___x_785_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_786_: u8 = 0;
                                        v___x_785_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__20;
                                        leanh::lean_inc(v___x_767_);
                                        v___x_786_ = l_Lean_Syntax_isOfKind(v___x_767_, v___x_785_);
                                        if v___x_786_ == 0 {
                                            let mut v___x_787_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_788_: u8 = 0;
                                            v___x_787_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__22;
                                            leanh::lean_inc(v___x_767_);
                                            v___x_788_ =
                                                l_Lean_Syntax_isOfKind(v___x_767_, v___x_787_);
                                            if v___x_788_ == 0 {
                                                let mut v___x_789_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_790_: u8 = 0;
                                                v___x_789_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__24;
                                                leanh::lean_inc(v___x_767_);
                                                v___x_790_ =
                                                    l_Lean_Syntax_isOfKind(v___x_767_, v___x_789_);
                                                if v___x_790_ == 0 {
                                                    let mut v___x_791_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v___x_792_: u8 = 0;
                                                    v___x_791_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__26;
                                                    leanh::lean_inc(v___x_767_);
                                                    v___x_792_ = l_Lean_Syntax_isOfKind(
                                                        v___x_767_, v___x_791_,
                                                    );
                                                    if v___x_792_ == 0 {
                                                        let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                        let mut v___x_794_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                        leanh::lean_dec(v___x_767_);
                                                        leanh::lean_dec(v___x_765_);
                                                        v___x_793_ = leanh::lean_box(1);
                                                        v___x_794_ = leanh::lean_alloc_ctor(
                                                            1,
                                                            2,
                                                            (0) as u32,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_794_, 0, v___x_793_,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_794_, 1, v_a_759_,
                                                        );
                                                        return v___x_794_;
                                                    } else {
                                                        let mut v_quotContext_795_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                        let mut v_currMacroScope_796_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                        let mut v_ref_797_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                                                        v_quotContext_795_ =
                                                            leanh::lean_ctor_get(
                                                                v_a_758_, 1,
                                                            );
                                                        v_currMacroScope_796_ =
                                                            leanh::lean_ctor_get(
                                                                v_a_758_, 2,
                                                            );
                                                        v_ref_797_ = leanh::lean_ctor_get(
                                                            v_a_758_, 5,
                                                        );
                                                        v___x_798_ = l_Lean_Syntax_getArg(
                                                            v___x_767_, v___x_764_,
                                                        );
                                                        v___x_799_ = l_Lean_Syntax_getArg(
                                                            v___x_767_, v___x_766_,
                                                        );
                                                        leanh::lean_dec(v___x_767_);
                                                        v___x_800_ = l_Lean_SourceInfo_fromRef(
                                                            v_ref_797_, v___x_790_,
                                                        );
                                                        v___x_801_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__31;
                                                        v___x_802_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__33), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__33_once), _init_l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__33);
                                                        v___x_803_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__37;
                                                        leanh::lean_inc(
                                                            v_currMacroScope_796_,
                                                        );
                                                        leanh::lean_inc(v_quotContext_795_);
                                                        v___x_804_ = l_Lean_addMacroScope(
                                                            v_quotContext_795_,
                                                            v___x_803_,
                                                            v_currMacroScope_796_,
                                                        );
                                                        v___x_805_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__40;
                                                        leanh::lean_inc_n(v___x_800_, 4);
                                                        v___x_806_ = leanh::lean_alloc_ctor(
                                                            3,
                                                            4,
                                                            (0) as u32,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_806_, 0, v___x_800_,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_806_, 1, v___x_802_,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_806_, 2, v___x_804_,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_806_, 3, v___x_805_,
                                                        );
                                                        v___x_807_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__42;
                                                        v___x_808_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__43;
                                                        v___x_809_ = leanh::lean_alloc_ctor(
                                                            2,
                                                            2,
                                                            (0) as u32,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_809_, 0, v___x_800_,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_809_, 1, v___x_808_,
                                                        );
                                                        v___x_810_ = l_Lean_Syntax_node3(
                                                            v___x_800_, v___x_791_, v___x_798_,
                                                            v___x_809_, v___x_799_,
                                                        );
                                                        v___x_811_ = l_Lean_Syntax_node2(
                                                            v___x_800_, v___x_807_, v___x_765_,
                                                            v___x_810_,
                                                        );
                                                        v___x_812_ = l_Lean_Syntax_node2(
                                                            v___x_800_, v___x_801_, v___x_806_,
                                                            v___x_811_,
                                                        );
                                                        v___x_813_ = leanh::lean_alloc_ctor(
                                                            0,
                                                            2,
                                                            (0) as u32,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_813_, 0, v___x_812_,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_813_, 1, v_a_759_,
                                                        );
                                                        return v___x_813_;
                                                    }
                                                } else {
                                                    let mut v_quotContext_814_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v_currMacroScope_815_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v_ref_816_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                                                    v_quotContext_814_ =
                                                        leanh::lean_ctor_get(v_a_758_, 1);
                                                    v_currMacroScope_815_ =
                                                        leanh::lean_ctor_get(v_a_758_, 2);
                                                    v_ref_816_ =
                                                        leanh::lean_ctor_get(v_a_758_, 5);
                                                    v___x_817_ = l_Lean_Syntax_getArg(
                                                        v___x_767_, v___x_764_,
                                                    );
                                                    v___x_818_ = l_Lean_Syntax_getArg(
                                                        v___x_767_, v___x_766_,
                                                    );
                                                    leanh::lean_dec(v___x_767_);
                                                    v___x_819_ = l_Lean_SourceInfo_fromRef(
                                                        v_ref_816_, v___x_788_,
                                                    );
                                                    v___x_820_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__31;
                                                    v___x_821_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__45), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__45_once), _init_l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__45);
                                                    v___x_822_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__47;
                                                    leanh::lean_inc(v_currMacroScope_815_);
                                                    leanh::lean_inc(v_quotContext_814_);
                                                    v___x_823_ = l_Lean_addMacroScope(
                                                        v_quotContext_814_,
                                                        v___x_822_,
                                                        v_currMacroScope_815_,
                                                    );
                                                    v___x_824_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__50;
                                                    leanh::lean_inc_n(v___x_819_, 4);
                                                    v___x_825_ = leanh::lean_alloc_ctor(
                                                        3,
                                                        4,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_825_, 0, v___x_819_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_825_, 1, v___x_821_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_825_, 2, v___x_823_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_825_, 3, v___x_824_,
                                                    );
                                                    v___x_826_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__42;
                                                    v___x_827_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__51;
                                                    v___x_828_ = leanh::lean_alloc_ctor(
                                                        2,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_828_, 0, v___x_819_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_828_, 1, v___x_827_,
                                                    );
                                                    v___x_829_ = l_Lean_Syntax_node3(
                                                        v___x_819_, v___x_789_, v___x_817_,
                                                        v___x_828_, v___x_818_,
                                                    );
                                                    v___x_830_ = l_Lean_Syntax_node2(
                                                        v___x_819_, v___x_826_, v___x_765_,
                                                        v___x_829_,
                                                    );
                                                    v___x_831_ = l_Lean_Syntax_node2(
                                                        v___x_819_, v___x_820_, v___x_825_,
                                                        v___x_830_,
                                                    );
                                                    v___x_832_ = leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_832_, 0, v___x_831_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_832_, 1, v_a_759_,
                                                    );
                                                    return v___x_832_;
                                                }
                                            } else {
                                                let mut v_quotContext_833_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                let mut v_currMacroScope_834_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                let mut v_ref_835_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_836_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_837_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_838_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_839_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_840_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_841_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_842_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_843_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_844_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_845_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_846_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_847_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_848_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_849_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_850_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                v_quotContext_833_ =
                                                    leanh::lean_ctor_get(v_a_758_, 1);
                                                v_currMacroScope_834_ =
                                                    leanh::lean_ctor_get(v_a_758_, 2);
                                                v_ref_835_ =
                                                    leanh::lean_ctor_get(v_a_758_, 5);
                                                v___x_836_ =
                                                    l_Lean_Syntax_getArg(v___x_767_, v___x_774_);
                                                leanh::lean_dec(v___x_767_);
                                                v___x_837_ = l_Lean_SourceInfo_fromRef(
                                                    v_ref_835_, v___x_786_,
                                                );
                                                v___x_838_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__31;
                                                v___x_839_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__53), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__53_once), _init_l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__53);
                                                v___x_840_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__55;
                                                leanh::lean_inc(v_currMacroScope_834_);
                                                leanh::lean_inc(v_quotContext_833_);
                                                v___x_841_ = l_Lean_addMacroScope(
                                                    v_quotContext_833_,
                                                    v___x_840_,
                                                    v_currMacroScope_834_,
                                                );
                                                v___x_842_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__58;
                                                leanh::lean_inc_n(v___x_837_, 4);
                                                v___x_843_ =
                                                    leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_843_, 0, v___x_837_,
                                                );
                                                leanh::lean_ctor_set(
                                                    v___x_843_, 1, v___x_839_,
                                                );
                                                leanh::lean_ctor_set(
                                                    v___x_843_, 2, v___x_841_,
                                                );
                                                leanh::lean_ctor_set(
                                                    v___x_843_, 3, v___x_842_,
                                                );
                                                v___x_844_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__42;
                                                v___x_845_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__59;
                                                v___x_846_ =
                                                    leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_846_, 0, v___x_837_,
                                                );
                                                leanh::lean_ctor_set(
                                                    v___x_846_, 1, v___x_845_,
                                                );
                                                v___x_847_ = l_Lean_Syntax_node2(
                                                    v___x_837_, v___x_787_, v___x_846_, v___x_836_,
                                                );
                                                v___x_848_ = l_Lean_Syntax_node2(
                                                    v___x_837_, v___x_844_, v___x_765_, v___x_847_,
                                                );
                                                v___x_849_ = l_Lean_Syntax_node2(
                                                    v___x_837_, v___x_838_, v___x_843_, v___x_848_,
                                                );
                                                v___x_850_ =
                                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_850_, 0, v___x_849_,
                                                );
                                                leanh::lean_ctor_set(
                                                    v___x_850_, 1, v_a_759_,
                                                );
                                                return v___x_850_;
                                            }
                                        } else {
                                            let mut v_quotContext_851_: *mut leanh::LeanObject = core::ptr::null_mut();
                                            let mut v_currMacroScope_852_: *mut leanh::LeanObject = core::ptr::null_mut();
                                            let mut v_ref_853_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_854_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_855_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_856_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_857_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_858_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_859_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_860_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_861_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_862_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_863_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_864_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_865_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_866_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_867_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_868_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_869_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            v_quotContext_851_ =
                                                leanh::lean_ctor_get(v_a_758_, 1);
                                            v_currMacroScope_852_ =
                                                leanh::lean_ctor_get(v_a_758_, 2);
                                            v_ref_853_ = leanh::lean_ctor_get(v_a_758_, 5);
                                            v___x_854_ =
                                                l_Lean_Syntax_getArg(v___x_767_, v___x_764_);
                                            v___x_855_ =
                                                l_Lean_Syntax_getArg(v___x_767_, v___x_766_);
                                            leanh::lean_dec(v___x_767_);
                                            v___x_856_ =
                                                l_Lean_SourceInfo_fromRef(v_ref_853_, v___x_784_);
                                            v___x_857_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__31;
                                            v___x_858_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__61), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__61_once), _init_l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__61);
                                            v___x_859_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__63;
                                            leanh::lean_inc(v_currMacroScope_852_);
                                            leanh::lean_inc(v_quotContext_851_);
                                            v___x_860_ = l_Lean_addMacroScope(
                                                v_quotContext_851_,
                                                v___x_859_,
                                                v_currMacroScope_852_,
                                            );
                                            v___x_861_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__66;
                                            leanh::lean_inc_n(v___x_856_, 4);
                                            v___x_862_ =
                                                leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                            leanh::lean_ctor_set(v___x_862_, 0, v___x_856_);
                                            leanh::lean_ctor_set(v___x_862_, 1, v___x_858_);
                                            leanh::lean_ctor_set(v___x_862_, 2, v___x_860_);
                                            leanh::lean_ctor_set(v___x_862_, 3, v___x_861_);
                                            v___x_863_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__42;
                                            v___x_864_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__67;
                                            v___x_865_ =
                                                leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                            leanh::lean_ctor_set(v___x_865_, 0, v___x_856_);
                                            leanh::lean_ctor_set(v___x_865_, 1, v___x_864_);
                                            v___x_866_ = l_Lean_Syntax_node3(
                                                v___x_856_, v___x_779_, v___x_854_, v___x_865_,
                                                v___x_855_,
                                            );
                                            v___x_867_ = l_Lean_Syntax_node2(
                                                v___x_856_, v___x_863_, v___x_765_, v___x_866_,
                                            );
                                            v___x_868_ = l_Lean_Syntax_node2(
                                                v___x_856_, v___x_857_, v___x_862_, v___x_867_,
                                            );
                                            v___x_869_ =
                                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                            leanh::lean_ctor_set(v___x_869_, 0, v___x_868_);
                                            leanh::lean_ctor_set(v___x_869_, 1, v_a_759_);
                                            return v___x_869_;
                                        }
                                    } else {
                                        let mut v_quotContext_870_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v_currMacroScope_871_: *mut leanh::LeanObject = core::ptr::null_mut();
                                        let mut v_ref_872_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_873_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_874_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_875_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_876_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_877_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_878_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_879_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_880_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_881_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_882_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_883_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_884_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_885_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_886_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_887_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_888_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        v_quotContext_870_ =
                                            leanh::lean_ctor_get(v_a_758_, 1);
                                        v_currMacroScope_871_ =
                                            leanh::lean_ctor_get(v_a_758_, 2);
                                        v_ref_872_ = leanh::lean_ctor_get(v_a_758_, 5);
                                        v___x_873_ = l_Lean_Syntax_getArg(v___x_767_, v___x_764_);
                                        v___x_874_ = l_Lean_Syntax_getArg(v___x_767_, v___x_766_);
                                        leanh::lean_dec(v___x_767_);
                                        v___x_875_ =
                                            l_Lean_SourceInfo_fromRef(v_ref_872_, v___x_782_);
                                        v___x_876_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__31;
                                        v___x_877_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__69), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__69_once), _init_l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__69);
                                        v___x_878_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__71;
                                        leanh::lean_inc(v_currMacroScope_871_);
                                        leanh::lean_inc(v_quotContext_870_);
                                        v___x_879_ = l_Lean_addMacroScope(
                                            v_quotContext_870_,
                                            v___x_878_,
                                            v_currMacroScope_871_,
                                        );
                                        v___x_880_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__74;
                                        leanh::lean_inc_n(v___x_875_, 4);
                                        v___x_881_ =
                                            leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                        leanh::lean_ctor_set(v___x_881_, 0, v___x_875_);
                                        leanh::lean_ctor_set(v___x_881_, 1, v___x_877_);
                                        leanh::lean_ctor_set(v___x_881_, 2, v___x_879_);
                                        leanh::lean_ctor_set(v___x_881_, 3, v___x_880_);
                                        v___x_882_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__42;
                                        v___x_883_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__75;
                                        v___x_884_ =
                                            leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_884_, 0, v___x_875_);
                                        leanh::lean_ctor_set(v___x_884_, 1, v___x_883_);
                                        v___x_885_ = l_Lean_Syntax_node3(
                                            v___x_875_, v___x_777_, v___x_873_, v___x_884_,
                                            v___x_874_,
                                        );
                                        v___x_886_ = l_Lean_Syntax_node2(
                                            v___x_875_, v___x_882_, v___x_765_, v___x_885_,
                                        );
                                        v___x_887_ = l_Lean_Syntax_node2(
                                            v___x_875_, v___x_876_, v___x_881_, v___x_886_,
                                        );
                                        v___x_888_ =
                                            leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_888_, 0, v___x_887_);
                                        leanh::lean_ctor_set(v___x_888_, 1, v_a_759_);
                                        return v___x_888_;
                                    }
                                } else {
                                    let mut v_quotContext_889_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v_currMacroScope_890_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v_ref_891_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_892_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_893_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_894_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_895_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_896_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_897_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_898_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_899_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_900_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_901_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_902_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_903_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_904_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_905_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_906_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    v_quotContext_889_ = leanh::lean_ctor_get(v_a_758_, 1);
                                    v_currMacroScope_890_ =
                                        leanh::lean_ctor_get(v_a_758_, 2);
                                    v_ref_891_ = leanh::lean_ctor_get(v_a_758_, 5);
                                    v___x_892_ = l_Lean_Syntax_getArg(v___x_767_, v___x_774_);
                                    leanh::lean_dec(v___x_767_);
                                    v___x_893_ = l_Lean_SourceInfo_fromRef(v_ref_891_, v___x_780_);
                                    v___x_894_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__31;
                                    v___x_895_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__77), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__77_once), _init_l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__77);
                                    v___x_896_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__79;
                                    leanh::lean_inc(v_currMacroScope_890_);
                                    leanh::lean_inc(v_quotContext_889_);
                                    v___x_897_ = l_Lean_addMacroScope(
                                        v_quotContext_889_,
                                        v___x_896_,
                                        v_currMacroScope_890_,
                                    );
                                    v___x_898_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__82;
                                    leanh::lean_inc_n(v___x_893_, 4);
                                    v___x_899_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                    leanh::lean_ctor_set(v___x_899_, 0, v___x_893_);
                                    leanh::lean_ctor_set(v___x_899_, 1, v___x_895_);
                                    leanh::lean_ctor_set(v___x_899_, 2, v___x_897_);
                                    leanh::lean_ctor_set(v___x_899_, 3, v___x_898_);
                                    v___x_900_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__42;
                                    v___x_901_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__83;
                                    v___x_902_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_902_, 0, v___x_893_);
                                    leanh::lean_ctor_set(v___x_902_, 1, v___x_901_);
                                    v___x_903_ = l_Lean_Syntax_node2(
                                        v___x_893_, v___x_775_, v___x_902_, v___x_892_,
                                    );
                                    v___x_904_ = l_Lean_Syntax_node2(
                                        v___x_893_, v___x_900_, v___x_765_, v___x_903_,
                                    );
                                    v___x_905_ = l_Lean_Syntax_node2(
                                        v___x_893_, v___x_894_, v___x_899_, v___x_904_,
                                    );
                                    v___x_906_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_906_, 0, v___x_905_);
                                    leanh::lean_ctor_set(v___x_906_, 1, v_a_759_);
                                    return v___x_906_;
                                }
                            } else {
                                let mut v_quotContext_907_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v_currMacroScope_908_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v_ref_909_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_910_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_911_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_912_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_913_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_914_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_915_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_916_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_917_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_918_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_919_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_920_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_921_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_922_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_923_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_924_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_925_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                v_quotContext_907_ = leanh::lean_ctor_get(v_a_758_, 1);
                                v_currMacroScope_908_ = leanh::lean_ctor_get(v_a_758_, 2);
                                v_ref_909_ = leanh::lean_ctor_get(v_a_758_, 5);
                                v___x_910_ = l_Lean_Syntax_getArg(v___x_767_, v___x_764_);
                                v___x_911_ = l_Lean_Syntax_getArg(v___x_767_, v___x_766_);
                                leanh::lean_dec(v___x_767_);
                                v___x_912_ = l_Lean_SourceInfo_fromRef(v_ref_909_, v___x_778_);
                                v___x_913_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__31;
                                v___x_914_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__61), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__61_once), _init_l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__61);
                                v___x_915_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__63;
                                leanh::lean_inc(v_currMacroScope_908_);
                                leanh::lean_inc(v_quotContext_907_);
                                v___x_916_ = l_Lean_addMacroScope(
                                    v_quotContext_907_,
                                    v___x_915_,
                                    v_currMacroScope_908_,
                                );
                                v___x_917_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__66;
                                leanh::lean_inc_n(v___x_912_, 4);
                                v___x_918_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                leanh::lean_ctor_set(v___x_918_, 0, v___x_912_);
                                leanh::lean_ctor_set(v___x_918_, 1, v___x_914_);
                                leanh::lean_ctor_set(v___x_918_, 2, v___x_916_);
                                leanh::lean_ctor_set(v___x_918_, 3, v___x_917_);
                                v___x_919_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__42;
                                v___x_920_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__67;
                                v___x_921_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_921_, 0, v___x_912_);
                                leanh::lean_ctor_set(v___x_921_, 1, v___x_920_);
                                v___x_922_ = l_Lean_Syntax_node3(
                                    v___x_912_, v___x_779_, v___x_910_, v___x_921_, v___x_911_,
                                );
                                v___x_923_ = l_Lean_Syntax_node2(
                                    v___x_912_, v___x_919_, v___x_765_, v___x_922_,
                                );
                                v___x_924_ = l_Lean_Syntax_node2(
                                    v___x_912_, v___x_913_, v___x_918_, v___x_923_,
                                );
                                v___x_925_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_925_, 0, v___x_924_);
                                leanh::lean_ctor_set(v___x_925_, 1, v_a_759_);
                                return v___x_925_;
                            }
                        } else {
                            let mut v_quotContext_926_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_currMacroScope_927_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_ref_928_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_929_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_930_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_931_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_932_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_933_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_934_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_935_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_936_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_937_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_938_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_939_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_940_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_941_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_942_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_943_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_944_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            v_quotContext_926_ = leanh::lean_ctor_get(v_a_758_, 1);
                            v_currMacroScope_927_ = leanh::lean_ctor_get(v_a_758_, 2);
                            v_ref_928_ = leanh::lean_ctor_get(v_a_758_, 5);
                            v___x_929_ = l_Lean_Syntax_getArg(v___x_767_, v___x_764_);
                            v___x_930_ = l_Lean_Syntax_getArg(v___x_767_, v___x_766_);
                            leanh::lean_dec(v___x_767_);
                            v___x_931_ = l_Lean_SourceInfo_fromRef(v_ref_928_, v___x_776_);
                            v___x_932_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__31;
                            v___x_933_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__69), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__69_once), _init_l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__69);
                            v___x_934_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__71;
                            leanh::lean_inc(v_currMacroScope_927_);
                            leanh::lean_inc(v_quotContext_926_);
                            v___x_935_ = l_Lean_addMacroScope(
                                v_quotContext_926_,
                                v___x_934_,
                                v_currMacroScope_927_,
                            );
                            v___x_936_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__74;
                            leanh::lean_inc_n(v___x_931_, 4);
                            v___x_937_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_937_, 0, v___x_931_);
                            leanh::lean_ctor_set(v___x_937_, 1, v___x_933_);
                            leanh::lean_ctor_set(v___x_937_, 2, v___x_935_);
                            leanh::lean_ctor_set(v___x_937_, 3, v___x_936_);
                            v___x_938_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__42;
                            v___x_939_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__75;
                            v___x_940_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_940_, 0, v___x_931_);
                            leanh::lean_ctor_set(v___x_940_, 1, v___x_939_);
                            v___x_941_ = l_Lean_Syntax_node3(
                                v___x_931_, v___x_777_, v___x_929_, v___x_940_, v___x_930_,
                            );
                            v___x_942_ =
                                l_Lean_Syntax_node2(v___x_931_, v___x_938_, v___x_765_, v___x_941_);
                            v___x_943_ =
                                l_Lean_Syntax_node2(v___x_931_, v___x_932_, v___x_937_, v___x_942_);
                            v___x_944_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_944_, 0, v___x_943_);
                            leanh::lean_ctor_set(v___x_944_, 1, v_a_759_);
                            return v___x_944_;
                        }
                    } else {
                        let mut v_quotContext_945_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_currMacroScope_946_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_ref_947_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                        v_quotContext_945_ = leanh::lean_ctor_get(v_a_758_, 1);
                        v_currMacroScope_946_ = leanh::lean_ctor_get(v_a_758_, 2);
                        v_ref_947_ = leanh::lean_ctor_get(v_a_758_, 5);
                        v___x_948_ = l_Lean_Syntax_getArg(v___x_767_, v___x_774_);
                        leanh::lean_dec(v___x_767_);
                        v___x_949_ = l_Lean_SourceInfo_fromRef(v_ref_947_, v___x_773_);
                        v___x_950_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__31;
                        v___x_951_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__77), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__77_once), _init_l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__77);
                        v___x_952_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__79;
                        leanh::lean_inc(v_currMacroScope_946_);
                        leanh::lean_inc(v_quotContext_945_);
                        v___x_953_ = l_Lean_addMacroScope(
                            v_quotContext_945_,
                            v___x_952_,
                            v_currMacroScope_946_,
                        );
                        v___x_954_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__82;
                        leanh::lean_inc_n(v___x_949_, 4);
                        v___x_955_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                        leanh::lean_ctor_set(v___x_955_, 0, v___x_949_);
                        leanh::lean_ctor_set(v___x_955_, 1, v___x_951_);
                        leanh::lean_ctor_set(v___x_955_, 2, v___x_953_);
                        leanh::lean_ctor_set(v___x_955_, 3, v___x_954_);
                        v___x_956_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__42;
                        v___x_957_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__83;
                        v___x_958_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_958_, 0, v___x_949_);
                        leanh::lean_ctor_set(v___x_958_, 1, v___x_957_);
                        v___x_959_ =
                            l_Lean_Syntax_node2(v___x_949_, v___x_775_, v___x_958_, v___x_948_);
                        v___x_960_ =
                            l_Lean_Syntax_node2(v___x_949_, v___x_956_, v___x_765_, v___x_959_);
                        v___x_961_ =
                            l_Lean_Syntax_node2(v___x_949_, v___x_950_, v___x_955_, v___x_960_);
                        v___x_962_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_962_, 0, v___x_961_);
                        leanh::lean_ctor_set(v___x_962_, 1, v_a_759_);
                        return v___x_962_;
                    }
                } else {
                    let mut v_quotContext_963_: *mut leanh::LeanObject =
                        core::ptr::null_mut();
                    let mut v_currMacroScope_964_: *mut leanh::LeanObject =
                        core::ptr::null_mut();
                    let mut v_ref_965_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                    v_quotContext_963_ = leanh::lean_ctor_get(v_a_758_, 1);
                    v_currMacroScope_964_ = leanh::lean_ctor_get(v_a_758_, 2);
                    v_ref_965_ = leanh::lean_ctor_get(v_a_758_, 5);
                    v___x_966_ = l_Lean_Syntax_getArg(v___x_767_, v___x_764_);
                    leanh::lean_dec(v___x_767_);
                    v___x_967_ = l_Lean_SourceInfo_fromRef(v_ref_965_, v___x_771_);
                    v___x_968_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__31;
                    v___x_969_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__85), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__85_once), _init_l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__85);
                    v___x_970_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__87;
                    leanh::lean_inc(v_currMacroScope_964_);
                    leanh::lean_inc(v_quotContext_963_);
                    v___x_971_ =
                        l_Lean_addMacroScope(v_quotContext_963_, v___x_970_, v_currMacroScope_964_);
                    v___x_972_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__90;
                    leanh::lean_inc_n(v___x_967_, 4);
                    v___x_973_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_973_, 0, v___x_967_);
                    leanh::lean_ctor_set(v___x_973_, 1, v___x_969_);
                    leanh::lean_ctor_set(v___x_973_, 2, v___x_971_);
                    leanh::lean_ctor_set(v___x_973_, 3, v___x_972_);
                    v___x_974_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__42;
                    v___x_975_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__91;
                    v___x_976_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_976_, 0, v___x_967_);
                    leanh::lean_ctor_set(v___x_976_, 1, v___x_975_);
                    v___x_977_ =
                        l_Lean_Syntax_node2(v___x_967_, v___x_772_, v___x_966_, v___x_976_);
                    v___x_978_ =
                        l_Lean_Syntax_node2(v___x_967_, v___x_974_, v___x_765_, v___x_977_);
                    v___x_979_ =
                        l_Lean_Syntax_node2(v___x_967_, v___x_968_, v___x_973_, v___x_978_);
                    v___x_980_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_980_, 0, v___x_979_);
                    leanh::lean_ctor_set(v___x_980_, 1, v_a_759_);
                    return v___x_980_;
                }
            } else {
                let mut v_quotContext_981_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_currMacroScope_982_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_ref_983_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                v_quotContext_981_ = leanh::lean_ctor_get(v_a_758_, 1);
                v_currMacroScope_982_ = leanh::lean_ctor_get(v_a_758_, 2);
                v_ref_983_ = leanh::lean_ctor_get(v_a_758_, 5);
                v___x_984_ = l_Lean_Syntax_getArg(v___x_767_, v___x_764_);
                leanh::lean_dec(v___x_767_);
                v___x_985_ = l_Lean_SourceInfo_fromRef(v_ref_983_, v___x_769_);
                v___x_986_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__31;
                v___x_987_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__93), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__93_once), _init_l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__93);
                v___x_988_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__95;
                leanh::lean_inc(v_currMacroScope_982_);
                leanh::lean_inc(v_quotContext_981_);
                v___x_989_ =
                    l_Lean_addMacroScope(v_quotContext_981_, v___x_988_, v_currMacroScope_982_);
                v___x_990_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__98;
                leanh::lean_inc_n(v___x_985_, 4);
                v___x_991_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_991_, 0, v___x_985_);
                leanh::lean_ctor_set(v___x_991_, 1, v___x_987_);
                leanh::lean_ctor_set(v___x_991_, 2, v___x_989_);
                leanh::lean_ctor_set(v___x_991_, 3, v___x_990_);
                v___x_992_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__42;
                v___x_993_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__99;
                v___x_994_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_994_, 0, v___x_985_);
                leanh::lean_ctor_set(v___x_994_, 1, v___x_993_);
                v___x_995_ = l_Lean_Syntax_node2(v___x_985_, v___x_770_, v___x_984_, v___x_994_);
                v___x_996_ = l_Lean_Syntax_node2(v___x_985_, v___x_992_, v___x_765_, v___x_995_);
                v___x_997_ = l_Lean_Syntax_node2(v___x_985_, v___x_986_, v___x_991_, v___x_996_);
                v___x_998_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_998_, 0, v___x_997_);
                leanh::lean_ctor_set(v___x_998_, 1, v_a_759_);
                return v___x_998_;
            }
        } else {
            let mut v_quotContext_999_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_ref_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1002_: u8 = 0;
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
            leanh::lean_dec(v___x_767_);
            v_quotContext_999_ = leanh::lean_ctor_get(v_a_758_, 1);
            v_currMacroScope_1000_ = leanh::lean_ctor_get(v_a_758_, 2);
            v_ref_1001_ = leanh::lean_ctor_get(v_a_758_, 5);
            v___x_1002_ = 0;
            v___x_1003_ = l_Lean_SourceInfo_fromRef(v_ref_1001_, v___x_1002_);
            v___x_1004_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__31;
            v___x_1005_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__101), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__101_once), _init_l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__101);
            v___x_1006_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__103;
            leanh::lean_inc(v_currMacroScope_1000_);
            leanh::lean_inc(v_quotContext_999_);
            v___x_1007_ =
                l_Lean_addMacroScope(v_quotContext_999_, v___x_1006_, v_currMacroScope_1000_);
            v___x_1008_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__106;
            leanh::lean_inc_n(v___x_1003_, 4);
            v___x_1009_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
            leanh::lean_ctor_set(v___x_1009_, 0, v___x_1003_);
            leanh::lean_ctor_set(v___x_1009_, 1, v___x_1005_);
            leanh::lean_ctor_set(v___x_1009_, 2, v___x_1007_);
            leanh::lean_ctor_set(v___x_1009_, 3, v___x_1008_);
            v___x_1010_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__42;
            v___x_1011_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___closed__107;
            v___x_1012_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1012_, 0, v___x_1003_);
            leanh::lean_ctor_set(v___x_1012_, 1, v___x_1011_);
            v___x_1013_ = l_Lean_Syntax_node1(v___x_1003_, v___x_768_, v___x_1012_);
            v___x_1014_ = l_Lean_Syntax_node2(v___x_1003_, v___x_1010_, v___x_765_, v___x_1013_);
            v___x_1015_ = l_Lean_Syntax_node2(v___x_1003_, v___x_1004_, v___x_1009_, v___x_1014_);
            v___x_1016_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1016_, 0, v___x_1015_);
            leanh::lean_ctor_set(v___x_1016_, 1, v_a_759_);
            return v___x_1016_;
        }
    }
}
pub unsafe fn l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1___boxed(
    mut v_x_1017_: *mut leanh::LeanObject,
    mut v_a_1018_: *mut leanh::LeanObject,
    mut v_a_1019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1020_ = l_Std___aux__Init__Data__Slice__Notation______macroRules__term_____x5b___x5d__1(
        v_x_1017_, v_a_1018_, v_a_1019_,
    );
    leanh::lean_dec_ref(v_a_1018_);
    return v_res_1020_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Slice_Notation(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_PRange(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Slice_Notation(
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
pub unsafe fn initialize_Init_Data_Slice_Notation(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Polymorphic_PRange(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Slice_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Slice_Notation(builtin);
}